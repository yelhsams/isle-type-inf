extern crate cranelift_isle;

use clap::{ArgAction, Parser};
use cranelift_isle::lexer::Lexer;
use cranelift_isle::parser::parse;
use cranelift_isle::sema::{self};
use cranelift_isle::sema::{Pattern, TermEnv, TermId, TypeEnv, VarId};
use easy_smt::SExprData;
use easy_smt::{Response, SExpr};
use itertools::Itertools;
use std::collections::{HashMap, HashSet};
use std::env;
use std::hash::Hash;
use std::path::PathBuf;
use strum::IntoEnumIterator;
use strum_macros::{EnumIter, FromRepr};
use type_inf::annotations::parse_annotations;
use type_inf::annotations::AnnotationEnv;
use type_inf::build_clif_lower_isle;
use type_inf::{FLAGS_WIDTH, REG_WIDTH};

use type_inf::termname::pattern_contains_termname;
use veri_ir::{annotation_ir, ConcreteTest, Expr, TermSignature, Type};

/* ----- STRUCTS FOR RECURSIVE RULE PARSING, TYPE CONVERSION ----- */
#[derive(Clone, Debug)]
struct RuleParseTree {
    // a map of var name to type variable, where var could be
    // Pattern::Var or var used in Pattern::BindPattern
    varid_to_type_var_map: HashMap<VarId, u32>,
    // a map of type var to value, if known
    type_var_to_val_map: HashMap<u32, i128>,
    // bookkeeping that tells the next unused type var
    next_type_var: u32,
    // combined constraints from all nodes
    concrete_constraints: HashSet<TypeExpr>,
    var_constraints: HashSet<TypeExpr>,
    bv_constraints: HashSet<TypeExpr>,

    ty_vars: HashMap<veri_ir::Expr, u32>,
    quantified_vars: HashMap<String, u32>,
    free_vars: HashMap<String, u32>,
    assumptions: Vec<Expr>,
    rhs_assertions: Vec<Expr>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
// Constraints either assign concrete types to type variables
// or set them equal to other type variables
enum TypeExpr {
    // Symbolic Sum for now. This only checks if the sum of bv widths of the lhs match the rhs.
    Symbolic(Vec<u32>, Vec<u32>),
    Concrete(u32, annotation_ir::Type),
    Variable(u32, u32),
    // The type variable of the first arg is equal to the value of the second
    WidthInt(u32, u32),
}

#[derive(Debug, Clone)]
pub struct AnnotationTypeInfo {
    // map of annotation variable to assigned type var
    pub term: String,
    pub var_to_type_var: HashMap<String, u32>,
}

#[derive(Debug)]
pub struct RuleSemantics {
    pub annotation_infos: Vec<AnnotationTypeInfo>,

    // map of type var to solved type
    pub type_var_to_type: HashMap<u32, annotation_ir::Type>,

    pub lhs: veri_ir::Expr,
    pub rhs: veri_ir::Expr,

    pub quantified_vars: Vec<veri_ir::BoundVar>,
    pub free_vars: Vec<veri_ir::BoundVar>,
    pub assumptions: Vec<Expr>,
    pub rhs_assertions: Vec<Expr>,
}

#[derive(Clone, Debug)]
pub struct TypeVarNode {
    ident: String,
    construct: TypeVarConstruct,
    type_var: u32,
    children: Vec<TypeVarNode>,
    assertions: Vec<veri_ir::Expr>,
}

#[derive(Clone, Debug)]
pub enum TypeVarConstruct {
    Var,
    BindPattern,
    Wildcard(u32),
    Term(TermId),
    Const(i128),
    Let(Vec<String>),
    And,
}

#[derive(Parser)]
#[clap(about, version, author)]
struct Args {
    /// Sets the input file
    #[clap(short, long)]
    input: Option<String>,

    /// Which LHS root to verify
    #[clap(short, long, default_value = "lower")]
    term: String,

    /// Which named rule to verify
    #[clap(long)]
    names: Option<Vec<String>>,

    /// Don't use the prelude ISLE files
    #[clap(short, long, action=ArgAction::SetTrue)]
    noprelude: bool,

    /// Include the aarch64 files
    #[clap(short, long, action=ArgAction::SetTrue)]
    aarch64: bool,
}

pub struct Config {
    /// Which LHS root to verify
    pub term: String,
    /// Which named rule to verify
    pub names: Option<Vec<String>>,
}

/* ----- CONVERT AST TO RULE SEMANTICS ----- */

fn convert_type(aty: &annotation_ir::Type) -> veri_ir::Type {
    match aty {
        annotation_ir::Type::BitVectorUnknown(..) => veri_ir::Type::BitVector(None),
        annotation_ir::Type::BitVector => veri_ir::Type::BitVector(None),
        annotation_ir::Type::BitVectorWithWidth(w) => veri_ir::Type::BitVector(Some(*w)),
        annotation_ir::Type::Int => veri_ir::Type::Int,
        annotation_ir::Type::Bool => veri_ir::Type::Bool,
        annotation_ir::Type::Poly(_) => veri_ir::Type::BitVector(None),
    }
}

fn type_to_num(aty: &annotation_ir::Type) -> String {
    match aty {
        annotation_ir::Type::BitVectorUnknown(..) => "bvunk".to_string(),
        annotation_ir::Type::BitVector => "bv".to_string(),
        annotation_ir::Type::BitVectorWithWidth(w) => format!("bv{}", &w),
        annotation_ir::Type::Int => "int".to_string(),
        annotation_ir::Type::Bool => "bool".to_string(),
        annotation_ir::Type::Poly(_) => "poly".to_string(),
    }
}

fn annotation_type_for_vir_type(ty: &Type) -> annotation_ir::Type {
    match ty {
        Type::BitVector(Some(x)) => annotation_ir::Type::BitVectorWithWidth(*x),
        Type::BitVector(None) => annotation_ir::Type::BitVector,
        Type::Bool => annotation_ir::Type::Bool,
        Type::Int => annotation_ir::Type::Int,
    }
}

pub fn type_rules_with_term_and_types(
    termenv: &TermEnv,
    typeenv: &TypeEnv,
    annotation_env: &AnnotationEnv,
    config: &Config,
    types: &TermSignature,
    concrete: &Option<ConcreteTest>,
) -> HashMap<sema::RuleId, RuleSemantics> {
    let mut solutions = HashMap::new();

    for rule in &termenv.rules {
        // Only type rules with the given term on the LHS
        if !pattern_contains_termname(
            // Hack for now: typeid not used
            &Pattern::Term(
                cranelift_isle::sema::TypeId(0),
                rule.root_term,
                rule.args.clone(),
            ),
            &config.term,
            termenv,
            typeenv,
        ) {
            continue;
        }
        if let Some(names) = &config.names {
            if rule.name.is_none() {
                continue;
            }
            let name = &typeenv.syms[rule.name.unwrap().index()];
            if !names.contains(name) {
                continue;
            }
        }
        if let Some(s) = type_annotations_using_rule(
            rule,
            annotation_env,
            typeenv,
            termenv,
            &config.term,
            &types,
            concrete,
        ) {
            // // Uncomment for debugging
            // for a in &s.annotation_infos {
            //     println!("{}", a.term);
            //     for (var, type_var) in &a.var_to_type_var {
            //         println!("{}: {:#?}", var, s.type_var_to_type[type_var]);
            //     }
            //     println!();
            // }
            solutions.insert(rule.id, s);
        }
    }
    solutions
}

fn type_annotations_using_rule<'a>(
    rule: &'a sema::Rule,
    annotation_env: &'a AnnotationEnv,
    typeenv: &'a TypeEnv,
    termenv: &'a TermEnv,
    term: &String,
    types: &TermSignature,
    _concrete: &'a Option<ConcreteTest>,
) -> Option<RuleSemantics> {
    let mut parse_tree = RuleParseTree {
        varid_to_type_var_map: HashMap::new(),
        type_var_to_val_map: HashMap::new(),
        next_type_var: 1,
        concrete_constraints: HashSet::new(),
        var_constraints: HashSet::new(),
        bv_constraints: HashSet::new(),
        ty_vars: HashMap::new(),
        quantified_vars: HashMap::new(),
        free_vars: HashMap::new(),
        assumptions: vec![],
        rhs_assertions: vec![],
    };
    let mut annotation_infos = vec![];
    if !rule.iflets.is_empty() {
        print!("\n\tif-lets:");
        for iflet in &rule.iflets {
            let iflet_lhs = &mut create_parse_tree_pattern(
                rule,
                &iflet.lhs,
                &mut parse_tree,
                typeenv,
                termenv,
                term,
                types,
            );
            let iflet_rhs =
                &mut create_parse_tree_expr(rule, &iflet.rhs, &mut parse_tree, typeenv, termenv);

            let iflet_lhs_expr = add_rule_constraints(
                &mut parse_tree,
                iflet_lhs,
                termenv,
                typeenv,
                annotation_env,
                &mut annotation_infos,
                false,
            );
            if iflet_lhs_expr.is_none() {
                return None;
            }

            let iflet_rhs_expr = add_rule_constraints(
                &mut parse_tree,
                iflet_rhs,
                termenv,
                typeenv,
                annotation_env,
                &mut annotation_infos,
                false,
            );
            if iflet_rhs_expr.is_none() {
                return None;
            }
            parse_tree
                .var_constraints
                .insert(TypeExpr::Variable(iflet_lhs.type_var, iflet_rhs.type_var));
            parse_tree.assumptions.push(veri_ir::Expr::Binary(
                veri_ir::BinaryOp::Eq,
                Box::new(iflet_lhs_expr.unwrap()),
                Box::new(iflet_rhs_expr.unwrap()),
            ));
        }
        print!("\n");
    }

    let lhs = &mut create_parse_tree_pattern(
        rule,
        // Hack for now: typeid not used
        &sema::Pattern::Term(
            cranelift_isle::sema::TypeId(0),
            rule.root_term,
            rule.args.clone(),
        ),
        &mut parse_tree,
        typeenv,
        termenv,
        term,
        types,
    );
    let rhs = &mut create_parse_tree_expr(rule, &rule.rhs, &mut parse_tree, typeenv, termenv);

    println!("Typing rule:");
    print!("\tLHS:");
    let lhs_expr = add_rule_constraints(
        &mut parse_tree,
        lhs,
        termenv,
        typeenv,
        annotation_env,
        &mut annotation_infos,
        false,
    );
    if lhs_expr.is_none() {
        return None;
    }
    print!("\n\tRHS:");
    let rhs_expr = add_rule_constraints(
        &mut parse_tree,
        rhs,
        termenv,
        typeenv,
        annotation_env,
        &mut annotation_infos,
        true,
    );
    if rhs_expr.is_none() {
        return None;
    }
    println!();

    match (lhs_expr, rhs_expr) {
        (Some(lhs_expr), Some(rhs_expr)) => {
            parse_tree
                .var_constraints
                .insert(TypeExpr::Variable(lhs.type_var, rhs.type_var));

            // NOTE: This is where SMT Solver should be called
            let (solution, _bv_unknown_width_sets) = solve_constraints(
                &parse_tree.concrete_constraints,
                &parse_tree.var_constraints,
                &parse_tree.bv_constraints,
                &mut parse_tree.type_var_to_val_map,
                &lhs_expr,
                &rhs_expr,
                // Some(&parse_tree.ty_vars),
            );

            // Print here?
            let smt = easy_smt::ContextBuilder::new()
                .replay_file(Some(std::fs::File::create("type_solver.smt2").unwrap()))
                .solver("z3", ["-smt2", "-in"])
                .build()
                .unwrap();

            let mut solver = TypeSolver::new(smt);
            let lhs = solver.display_isle_pattern(
                termenv,
                typeenv,
                rule,
                &annotation_infos,
                &solution,
                &Pattern::Term(
                    cranelift_isle::sema::TypeId(0),
                    rule.root_term,
                    rule.args.clone(),
                ),
                None,
            );
            println!("{}", solver.smt.display(lhs));

            println!("=>");
            let rhs = solver.display_isle_expr(
                termenv,
                typeenv,
                rule,
                &annotation_infos,
                &solution,
                &rule.rhs,
                None,
            );
            println!("{}", solver.smt.display(rhs));

            let mut tymap = HashMap::new();

            for (expr, t) in &parse_tree.ty_vars {
                if let Some(ty) = solution.get(&t) {
                    tymap.insert(*t, convert_type(ty));
                } else {
                    panic!("missing type variable {} in solution for: {:?}", t, expr);
                }
            }
            let mut quantified_vars = vec![];
            for (s, t) in parse_tree.quantified_vars.iter().sorted() {
                let expr = veri_ir::Expr::Terminal(veri_ir::Terminal::Var(s.clone()));
                if let Some(ty) = solution.get(t) {
                    let ty = convert_type(ty);
                    parse_tree.ty_vars.insert(expr, *t);
                    tymap.insert(*t, ty.clone());
                    quantified_vars.push(veri_ir::BoundVar {
                        name: s.clone(),
                        tyvar: *t,
                    });
                } else {
                    panic!("missing type variable {} in solution for: {:?}", t, expr);
                }
            }
            let mut free_vars = vec![];
            for (s, t) in parse_tree.free_vars {
                let expr = veri_ir::Expr::Terminal(veri_ir::Terminal::Var(s.clone()));
                if let Some(ty) = solution.get(&t) {
                    let ty = convert_type(ty);
                    parse_tree.ty_vars.insert(expr, t);
                    tymap.insert(t, ty.clone());
                    free_vars.push(veri_ir::BoundVar { name: s, tyvar: t });
                } else {
                    panic!("missing type variable {} in solution for: {:?}", t, expr);
                }
            }

            Some(RuleSemantics {
                annotation_infos,
                type_var_to_type: solution,
                lhs: lhs_expr,
                rhs: rhs_expr,
                quantified_vars,
                free_vars,
                assumptions: parse_tree.assumptions,
                rhs_assertions: parse_tree.rhs_assertions,
            })
        }
        _ => None,
    }
}

// Recursive process tree
fn create_parse_tree_pattern(
    rule: &sema::Rule,
    pattern: &sema::Pattern,
    tree: &mut RuleParseTree,
    typeenv: &TypeEnv,
    termenv: &TermEnv,
    term: &String,
    types: &TermSignature,
) -> TypeVarNode {
    match pattern {
        sema::Pattern::Term(_, term_id, args) => {
            let sym = termenv.terms[term_id.index()].name;
            let name = typeenv.syms[sym.index()].clone();

            // process children first
            let mut children = vec![];
            for (i, arg) in args.iter().enumerate() {
                let child =
                    create_parse_tree_pattern(rule, arg, tree, typeenv, termenv, term, types);

                // Our specified input term, use external types
                if name.eq(term) {
                    tree.concrete_constraints.insert(TypeExpr::Concrete(
                        child.type_var,
                        annotation_type_for_vir_type(&types.args[i]),
                    ));
                }
                children.push(child);
            }
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;

            if name.eq(term) {
                tree.concrete_constraints.insert(TypeExpr::Concrete(
                    type_var,
                    annotation_type_for_vir_type(&types.ret),
                ));
            }

            TypeVarNode {
                ident: format!("{}__{}", name, type_var),
                construct: TypeVarConstruct::Term(term_id.clone()),
                type_var,
                children,
                assertions: vec![],
            }
        }
        sema::Pattern::Var(_, var_id) => {
            let sym = rule.vars[var_id.index()].name;
            let ident = typeenv.syms[sym.index()].clone();

            let type_var = tree
                .varid_to_type_var_map
                .entry(*var_id)
                .or_insert(tree.next_type_var);
            if *type_var == tree.next_type_var {
                tree.next_type_var += 1;
            }
            let ident = format!("{}__clif{}__{}", ident, var_id.index(), *type_var);
            // this is a base case so there are no children
            TypeVarNode {
                ident,
                construct: TypeVarConstruct::Var,
                type_var: *type_var,
                children: vec![],
                assertions: vec![],
            }
        }
        sema::Pattern::BindPattern(_, var_id, subpat) => {
            let sym = rule.vars[var_id.index()].name;

            let type_var = *tree
                .varid_to_type_var_map
                .entry(*var_id)
                .or_insert(tree.next_type_var);
            if type_var == tree.next_type_var {
                tree.next_type_var += 1;
            }

            let ident = format!(
                "{}__clif{}__{}",
                typeenv.syms[sym.index()],
                var_id.index(),
                type_var
            );

            // this is a base case so there are no children
            let var_node = TypeVarNode {
                ident: ident.clone(),
                construct: TypeVarConstruct::Var,
                type_var: type_var,
                children: vec![],
                assertions: vec![],
            };

            let subpat_node =
                create_parse_tree_pattern(rule, subpat, tree, typeenv, termenv, term, types);

            let bind_type_var = tree.next_type_var;
            tree.next_type_var += 1;

            tree.var_constraints
                .insert(TypeExpr::Variable(type_var, subpat_node.type_var));
            tree.var_constraints
                .insert(TypeExpr::Variable(bind_type_var, type_var));
            tree.var_constraints
                .insert(TypeExpr::Variable(bind_type_var, subpat_node.type_var));

            TypeVarNode {
                ident,
                construct: TypeVarConstruct::BindPattern,
                type_var: type_var,
                children: vec![var_node, subpat_node],
                assertions: vec![],
            }
        }
        sema::Pattern::Wildcard(_) => {
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;
            TypeVarNode {
                ident: format!("wildcard__{}", type_var),
                construct: TypeVarConstruct::Wildcard(type_var),
                type_var: type_var,
                children: vec![],
                assertions: vec![],
            }
        }
        sema::Pattern::ConstPrim(_, sym) => {
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;
            let name = typeenv.syms[sym.index()].clone();
            let val = match name.as_str() {
                "I64" => 64,
                "I32" => 32,
                "I16" => 16,
                "I8" => 8,
                "true" => 1,
                "false" => 0,
                // Not currently used, but parsed
                "I128" => 16,
                _ => todo!("{:?}", &name),
            };
            let name = format!("{}__{}", name, type_var);

            TypeVarNode {
                ident: name,
                construct: TypeVarConstruct::Const(val),
                type_var,
                children: vec![],
                assertions: vec![],
            }
        }
        sema::Pattern::ConstInt(_, num) => {
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;
            let name = format!("{}__{}", num, type_var);
            TypeVarNode {
                ident: name,
                construct: TypeVarConstruct::Const(*num),
                type_var,
                children: vec![],
                assertions: vec![],
            }
        }
        sema::Pattern::And(_, subpats) => {
            let mut children = vec![];
            let mut ty_vars = vec![];
            for p in subpats {
                let child = create_parse_tree_pattern(rule, p, tree, typeenv, termenv, term, types);
                ty_vars.push(child.type_var);
                children.push(child);
            }
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;

            // Assert all sub type constraints are equivalent to the first subexpression
            let first = ty_vars[0];
            for e in &ty_vars[1..] {
                tree.var_constraints
                    .insert(TypeExpr::Variable(first, e.to_owned()));
            }

            TypeVarNode {
                ident: String::from("and"),
                construct: TypeVarConstruct::And,
                type_var,
                children,
                assertions: vec![],
            }
        }
    }
}

fn create_parse_tree_expr(
    rule: &sema::Rule,
    expr: &sema::Expr,
    tree: &mut RuleParseTree,
    typeenv: &TypeEnv,
    termenv: &TermEnv,
) -> TypeVarNode {
    match expr {
        sema::Expr::Term(_, term_id, args) => {
            let sym = termenv.terms[term_id.index()].name;
            let name = typeenv.syms[sym.index()].clone();

            // process children first
            let mut children = vec![];
            for arg in args {
                let child = create_parse_tree_expr(rule, arg, tree, typeenv, termenv);
                children.push(child);
            }
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;

            TypeVarNode {
                ident: format!("{}__{}", name, type_var),
                construct: TypeVarConstruct::Term(term_id.clone()),
                type_var,
                children,
                assertions: vec![],
            }
        }
        sema::Expr::Var(_, var_id) => {
            let mut ident = var_id.0.to_string();
            if var_id.index() < rule.vars.len() {
                let sym = rule.vars[var_id.index()].name;
                ident = typeenv.syms[sym.index()].clone();
            } else {
                println!("var {} not found, using var id instead", var_id.0);
                ident = format!("v{}", ident);
            }

            let type_var = tree
                .varid_to_type_var_map
                .entry(*var_id)
                .or_insert(tree.next_type_var);
            if *type_var == tree.next_type_var {
                tree.next_type_var += 1;
            }
            let ident = format!("{}__clif{}__{}", ident, var_id.index(), *type_var);
            // this is a base case so there are no children
            TypeVarNode {
                ident,
                construct: TypeVarConstruct::Var,
                type_var: *type_var,
                children: vec![],
                assertions: vec![],
            }
        }
        sema::Expr::ConstPrim(_, sym) => {
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;
            let name = typeenv.syms[sym.index()].clone();
            let val = match name.as_str() {
                "I8" => 8,
                "I64" => 64,
                "I32" => 32,
                "false" => 0,
                "true" => 1,
                _ => todo!("{:?}", &name),
            };
            let name = format!("{}__{}", name, type_var);
            TypeVarNode {
                ident: name,
                construct: TypeVarConstruct::Const(val),
                type_var,
                children: vec![],
                assertions: vec![],
            }
        }
        sema::Expr::ConstInt(_, num) => {
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;
            let name = format!("{}__{}", num, type_var);
            TypeVarNode {
                ident: name,
                construct: TypeVarConstruct::Const(*num),
                type_var,
                children: vec![],
                assertions: vec![],
            }
        }
        sema::Expr::Let { bindings, body, .. } => {
            let mut children = vec![];
            let mut bound = vec![];
            for (varid, _, expr) in bindings {
                let sym = rule.vars[varid.index()].name;
                let var = typeenv.syms[sym.index()].clone();
                let subpat_node = create_parse_tree_expr(rule, expr, tree, typeenv, termenv);

                let ty_var = tree.next_type_var;
                tree.next_type_var += 1;

                tree.var_constraints
                    .insert(TypeExpr::Variable(ty_var, subpat_node.type_var));

                tree.varid_to_type_var_map.insert(*varid, ty_var);
                children.push(subpat_node);
                let ident = format!("{}__clif{}__{}", var, varid.index(), ty_var);
                tree.quantified_vars.insert(ident.clone(), ty_var);
                bound.push(ident);
            }
            let body = create_parse_tree_expr(rule, body, tree, typeenv, termenv);
            let body_var = body.type_var;
            children.push(body);

            let type_var = tree.next_type_var;
            tree.next_type_var += 1;

            let name = format!("let__{}", type_var);

            // The let should have the same type as the body
            tree.var_constraints
                .insert(TypeExpr::Variable(type_var, body_var));

            TypeVarNode {
                ident: name,
                construct: TypeVarConstruct::Let(bound),
                type_var,
                children,
                assertions: vec![],
            }
        }
    }
}

fn const_fold_to_int(e: &veri_ir::Expr) -> Option<i128> {
    match e {
        Expr::Terminal(veri_ir::Terminal::Const(c, _)) => Some(*c),
        _ => None,
    }
}

fn add_annotation_constraints(
    expr: annotation_ir::Expr,
    tree: &mut RuleParseTree,
    annotation_info: &mut AnnotationTypeInfo,
) -> (veri_ir::Expr, u32) {
    let (e, t) = match expr {
        annotation_ir::Expr::Var(x, ..) => {
            let mut t = tree.next_type_var;
            if annotation_info.var_to_type_var.contains_key(&x) {
                t = annotation_info.var_to_type_var[&x];
            } else {
                annotation_info.var_to_type_var.insert(x.clone(), t);
                tree.next_type_var += 1;
            }
            let name = format!("{}__{}__{}", annotation_info.term, x, t);

            // Support the introduction of extra variables in the specification.
            //
            // TODO(mbm): understand whether this needs to be in quantified, free or both?
            tree.quantified_vars.insert(name.clone(), t);
            tree.free_vars.insert(name.clone(), t);

            (veri_ir::Expr::Terminal(veri_ir::Terminal::Var(name)), t)
        }
        annotation_ir::Expr::Const(c, ..) => {
            let t = tree.next_type_var;
            let e = veri_ir::Expr::Terminal(veri_ir::Terminal::Const(c.value, t));
            match c.ty {
                annotation_ir::Type::BitVector => {
                    let ty = annotation_ir::Type::BitVectorWithWidth(c.width);
                    tree.concrete_constraints.insert(TypeExpr::Concrete(t, ty));
                }
                _ => {
                    tree.concrete_constraints
                        .insert(TypeExpr::Concrete(t, c.ty.clone()));
                }
            }
            tree.next_type_var += 1;

            // If constant is known, add the value to the tree. Useful for
            // capturing isleTypes
            tree.type_var_to_val_map.insert(t, c.value);
            (e, t)
        }
        annotation_ir::Expr::True => {
            let t = tree.next_type_var;
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));

            tree.next_type_var += 1;
            (veri_ir::Expr::Terminal(veri_ir::Terminal::True), t)
        }
        annotation_ir::Expr::False => {
            let t = tree.next_type_var;
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));

            tree.next_type_var += 1;
            (veri_ir::Expr::Terminal(veri_ir::Terminal::False), t)
        }

        annotation_ir::Expr::WidthOf(x) => {
            let (ex, tx) = add_annotation_constraints(*x.clone(), tree, annotation_info);
            let t = tree.next_type_var;
            tree.next_type_var += 1;
            tree.bv_constraints
                .insert(TypeExpr::Concrete(tx, annotation_ir::Type::BitVector));
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Int));
            tree.concrete_constraints.insert(TypeExpr::WidthInt(tx, t));
            (veri_ir::Expr::WidthOf(Box::new(ex)), t)
        }

        annotation_ir::Expr::Eq(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::Eq, Box::new(e1), Box::new(e2)),
                t,
            )
        }
        annotation_ir::Expr::Imp(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::Bool));
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t2, annotation_ir::Type::Bool));
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::Imp, Box::new(e1), Box::new(e2)),
                t,
            )
        }
        annotation_ir::Expr::Lte(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::Lte, Box::new(e1), Box::new(e2)),
                t,
            )
        }

        annotation_ir::Expr::Not(x) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::Bool));
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));

            tree.next_type_var += 1;
            (veri_ir::Expr::Unary(veri_ir::UnaryOp::Not, Box::new(e1)), t)
        }
        annotation_ir::Expr::Or(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::Bool));
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t2, annotation_ir::Type::Bool));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::Or, Box::new(e1), Box::new(e2)),
                t,
            )
        }
        annotation_ir::Expr::And(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::Bool));
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t2, annotation_ir::Type::Bool));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::And, Box::new(e1), Box::new(e2)),
                t,
            )
        }

        annotation_ir::Expr::BVSgt(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVSgt, Box::new(e1), Box::new(e2)),
                t,
            )
        }

        annotation_ir::Expr::BVSgte(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVSgte, Box::new(e1), Box::new(e2)),
                t,
            )
        }

        annotation_ir::Expr::BVSlt(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVSlt, Box::new(e1), Box::new(e2)),
                t,
            )
        }

        annotation_ir::Expr::BVSlte(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVSlte, Box::new(e1), Box::new(e2)),
                t,
            )
        }

        annotation_ir::Expr::BVUgt(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVUgt, Box::new(e1), Box::new(e2)),
                t,
            )
        }

        annotation_ir::Expr::BVUgte(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVUgte, Box::new(e1), Box::new(e2)),
                t,
            )
        }

        annotation_ir::Expr::BVUlt(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVUlt, Box::new(e1), Box::new(e2)),
                t,
            )
        }

        annotation_ir::Expr::BVUlte(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVUlte, Box::new(e1), Box::new(e2)),
                t,
            )
        }

        annotation_ir::Expr::BVSaddo(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVSaddo, Box::new(e1), Box::new(e2)),
                t,
            )
        }

        annotation_ir::Expr::BVNeg(x) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);

            let t = tree.next_type_var;
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Unary(veri_ir::UnaryOp::BVNeg, Box::new(e1)),
                t,
            )
        }
        annotation_ir::Expr::BVNot(x) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);

            let t = tree.next_type_var;
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Unary(veri_ir::UnaryOp::BVNot, Box::new(e1)),
                t,
            )
        }

        annotation_ir::Expr::BVMul(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t2, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));
            tree.var_constraints.insert(TypeExpr::Variable(t, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVMul, Box::new(e1), Box::new(e2)),
                t,
            )
        }
        annotation_ir::Expr::BVUDiv(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t2, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));
            tree.var_constraints.insert(TypeExpr::Variable(t, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVUDiv, Box::new(e1), Box::new(e2)),
                t,
            )
        }
        annotation_ir::Expr::BVSDiv(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t2, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));
            tree.var_constraints.insert(TypeExpr::Variable(t, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVSDiv, Box::new(e1), Box::new(e2)),
                t,
            )
        }
        annotation_ir::Expr::BVAdd(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t2, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));
            tree.var_constraints.insert(TypeExpr::Variable(t, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVAdd, Box::new(e1), Box::new(e2)),
                t,
            )
        }
        annotation_ir::Expr::BVSub(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t2, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));
            tree.var_constraints.insert(TypeExpr::Variable(t, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVSub, Box::new(e1), Box::new(e2)),
                t,
            )
        }
        annotation_ir::Expr::BVUrem(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t2, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));
            tree.var_constraints.insert(TypeExpr::Variable(t, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVUrem, Box::new(e1), Box::new(e2)),
                t,
            )
        }
        annotation_ir::Expr::BVSrem(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t2, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));
            tree.var_constraints.insert(TypeExpr::Variable(t, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVSrem, Box::new(e1), Box::new(e2)),
                t,
            )
        }

        annotation_ir::Expr::BVAnd(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t2, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));
            tree.var_constraints.insert(TypeExpr::Variable(t, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVAnd, Box::new(e1), Box::new(e2)),
                t,
            )
        }
        annotation_ir::Expr::BVOr(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t2, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));
            tree.var_constraints.insert(TypeExpr::Variable(t, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVOr, Box::new(e1), Box::new(e2)),
                t,
            )
        }
        annotation_ir::Expr::BVXor(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t2, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));
            tree.var_constraints.insert(TypeExpr::Variable(t, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVXor, Box::new(e1), Box::new(e2)),
                t,
            )
        }
        annotation_ir::Expr::BVRotl(x, a) => {
            let (xe, xt) = add_annotation_constraints(*x, tree, annotation_info);
            let (ae, at) = add_annotation_constraints(*a, tree, annotation_info);
            let t = tree.next_type_var;
            tree.next_type_var += 1;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(xt, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(at, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t, xt));

            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVRotl, Box::new(xe), Box::new(ae)),
                t,
            )
        }
        annotation_ir::Expr::BVRotr(x, a) => {
            let (xe, xt) = add_annotation_constraints(*x, tree, annotation_info);
            let (ae, at) = add_annotation_constraints(*a, tree, annotation_info);
            let t = tree.next_type_var;
            tree.next_type_var += 1;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(xt, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(at, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t, xt));

            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVRotr, Box::new(xe), Box::new(ae)),
                t,
            )
        }
        annotation_ir::Expr::BVShl(x, a) => {
            let (xe, xt) = add_annotation_constraints(*x, tree, annotation_info);
            let (ae, at) = add_annotation_constraints(*a, tree, annotation_info);
            let t = tree.next_type_var;
            tree.next_type_var += 1;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(xt, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(at, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t, xt));
            tree.var_constraints.insert(TypeExpr::Variable(xt, at));

            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVShl, Box::new(xe), Box::new(ae)),
                t,
            )
        }
        annotation_ir::Expr::BVShr(x, a) => {
            let (xe, xt) = add_annotation_constraints(*x, tree, annotation_info);
            let (ae, at) = add_annotation_constraints(*a, tree, annotation_info);
            let t = tree.next_type_var;
            tree.next_type_var += 1;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(xt, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(at, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t, xt));
            tree.var_constraints.insert(TypeExpr::Variable(xt, at));

            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVShr, Box::new(xe), Box::new(ae)),
                t,
            )
        }
        annotation_ir::Expr::BVAShr(x, a) => {
            let (xe, xt) = add_annotation_constraints(*x, tree, annotation_info);
            let (ae, at) = add_annotation_constraints(*a, tree, annotation_info);
            let t = tree.next_type_var;
            tree.next_type_var += 1;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(xt, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(at, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t, xt));
            tree.var_constraints.insert(TypeExpr::Variable(at, xt));

            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::BVAShr, Box::new(xe), Box::new(ae)),
                t,
            )
        }
        annotation_ir::Expr::Lt(x, y) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Binary(veri_ir::BinaryOp::Lt, Box::new(e1), Box::new(e2)),
                t,
            )
        }

        annotation_ir::Expr::BVConvTo(w, x) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let t = tree.next_type_var;
            tree.next_type_var += 1;

            let width = match *w {
                annotation_ir::Width::Const(x) => x,
                annotation_ir::Width::RegWidth => REG_WIDTH,
            };

            tree.concrete_constraints.insert(TypeExpr::Concrete(
                t,
                annotation_ir::Type::BitVectorWithWidth(width),
            ));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));

            (veri_ir::Expr::BVConvTo(Box::new(e1)), t)
        }
        annotation_ir::Expr::BVConvToVarWidth(w, x) => {
            let (we, wt) = add_annotation_constraints(*w, tree, annotation_info);
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let t = tree.next_type_var;
            tree.next_type_var += 1;

            // In the dynamic case, we don't know the width at this point
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(wt, annotation_ir::Type::Int));

            if let Some(w) = const_fold_to_int(&we) {
                tree.concrete_constraints.insert(TypeExpr::Concrete(
                    t,
                    annotation_ir::Type::BitVectorWithWidth(w.try_into().unwrap()),
                ));
                tree.bv_constraints
                    .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));

                (veri_ir::Expr::BVConvTo(Box::new(e1)), t)
            } else {
                tree.concrete_constraints.insert(TypeExpr::WidthInt(t, wt));
                tree.bv_constraints
                    .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
                tree.bv_constraints
                    .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));

                (
                    veri_ir::Expr::BVConvToVarWidth(Box::new(we), Box::new(e1)),
                    t,
                )
            }
        }
        annotation_ir::Expr::BVSignExtToVarWidth(w, x) => {
            let (we, wt) = add_annotation_constraints(*w, tree, annotation_info);
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let t = tree.next_type_var;
            tree.next_type_var += 1;

            // In the dynamic case, we don't know the width at this point
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(wt, annotation_ir::Type::Int));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));

            (
                veri_ir::Expr::BVSignExtToVarWidth(Box::new(we), Box::new(e1)),
                t,
            )
        }
        annotation_ir::Expr::BVZeroExtTo(w, x) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let t = tree.next_type_var;
            tree.next_type_var += 1;

            let width = match *w {
                veri_ir::annotation_ir::Width::Const(c) => c,
                veri_ir::annotation_ir::Width::RegWidth => REG_WIDTH,
            };

            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.concrete_constraints.insert(TypeExpr::Concrete(
                t,
                annotation_ir::Type::BitVectorWithWidth(width),
            ));

            (veri_ir::Expr::BVZeroExtTo(width, Box::new(e1)), t)
        }
        annotation_ir::Expr::BVZeroExtToVarWidth(w, x) => {
            let (we, wt) = add_annotation_constraints(*w, tree, annotation_info);
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let t = tree.next_type_var;
            tree.next_type_var += 1;

            // In the dynamic case, we don't know the width at this point
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(wt, annotation_ir::Type::Int));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));

            (
                veri_ir::Expr::BVZeroExtToVarWidth(Box::new(we), Box::new(e1)),
                t,
            )
        }
        annotation_ir::Expr::BVSignExtTo(w, x) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let t = tree.next_type_var;

            let width = match *w {
                veri_ir::annotation_ir::Width::Const(c) => c,
                veri_ir::annotation_ir::Width::RegWidth => REG_WIDTH,
            };

            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.concrete_constraints.insert(TypeExpr::Concrete(
                t,
                annotation_ir::Type::BitVectorWithWidth(width),
            ));

            tree.next_type_var += 1;

            (veri_ir::Expr::BVSignExtTo(width, Box::new(e1)), t)
        }
        annotation_ir::Expr::BVExtract(l, r, x) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let t = tree.next_type_var;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.concrete_constraints.insert(TypeExpr::Concrete(
                t,
                annotation_ir::Type::BitVectorWithWidth(l - r + 1),
            ));

            tree.next_type_var += 1;

            (veri_ir::Expr::BVExtract(l, r, Box::new(e1)), t)
        }
        annotation_ir::Expr::BVConcat(xs) => {
            // AVH todo: doesn't sum the various widths, has to be done in the solver
            let t = tree.next_type_var;
            tree.next_type_var += 1;

            let mut sum_bvs = vec![];

            let mut exprs = vec![];
            for x in xs {
                let (xe, xt) = add_annotation_constraints(x, tree, annotation_info);
                tree.bv_constraints
                    .insert(TypeExpr::Concrete(xt, annotation_ir::Type::BitVector));

                // add each bv to the sum_bv
                sum_bvs.push(xt);

                exprs.push(xe);
            }
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.concrete_constraints
                .insert(TypeExpr::Symbolic(sum_bvs, vec![t]));
            tree.next_type_var += 1;

            (veri_ir::Expr::BVConcat(exprs), t)
        }
        annotation_ir::Expr::BVIntToBv(w, x) => {
            let (ex, tx) = add_annotation_constraints(*x.clone(), tree, annotation_info);

            let t = tree.next_type_var;
            tree.next_type_var += 1;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(tx, annotation_ir::Type::Int));

            tree.concrete_constraints.insert(TypeExpr::Concrete(
                t,
                annotation_ir::Type::BitVectorWithWidth(w),
            ));

            (veri_ir::Expr::BVIntToBV(w, Box::new(ex)), t)
        }
        annotation_ir::Expr::BVToInt(x) => {
            let (ex, tx) = add_annotation_constraints(*x.clone(), tree, annotation_info);

            let t = tree.next_type_var;
            tree.next_type_var += 1;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(tx, annotation_ir::Type::BitVector));

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Int));

            (veri_ir::Expr::BVToInt(Box::new(ex)), t)
        }
        annotation_ir::Expr::Conditional(c, t, e) => {
            let (e1, t1) = add_annotation_constraints(*c, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*t, tree, annotation_info);
            let (e3, t3) = add_annotation_constraints(*e, tree, annotation_info);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::Bool));
            tree.var_constraints.insert(TypeExpr::Variable(t2, t3));
            tree.var_constraints.insert(TypeExpr::Variable(t, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::Conditional(Box::new(e1), Box::new(e2), Box::new(e3)),
                t,
            )
        }
        annotation_ir::Expr::Switch(c, cases) => {
            let (c_expr, c_t) = add_annotation_constraints(*c, tree, annotation_info);

            let t = tree.next_type_var;
            tree.next_type_var += 1;

            let mut case_exprs = vec![];
            for (m, b) in cases {
                let (case_expr, case_t) =
                    add_annotation_constraints(m.clone(), tree, annotation_info);
                let (body_expr, body_t) =
                    add_annotation_constraints(b.clone(), tree, annotation_info);

                tree.var_constraints.insert(TypeExpr::Variable(c_t, case_t));
                tree.var_constraints.insert(TypeExpr::Variable(t, body_t));
                case_exprs.push((case_expr, body_expr));
            }
            (veri_ir::Expr::Switch(Box::new(c_expr), case_exprs), t)
        }
        annotation_ir::Expr::CLZ(x) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);

            let t = tree.next_type_var;
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));

            tree.next_type_var += 1;
            (veri_ir::Expr::CLZ(Box::new(e1)), t)
        }
        annotation_ir::Expr::A64CLZ(ty, x) => {
            let (e0, t0) = add_annotation_constraints(*ty, tree, annotation_info);
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);

            let t = tree.next_type_var;
            tree.concrete_constraints.insert(TypeExpr::Concrete(
                t,
                annotation_ir::Type::BitVectorWithWidth(REG_WIDTH),
            ));
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t0, annotation_ir::Type::Int));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));

            tree.next_type_var += 1;
            (veri_ir::Expr::A64CLZ(Box::new(e0), Box::new(e1)), t)
        }
        annotation_ir::Expr::CLS(x) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);

            let t = tree.next_type_var;
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));

            tree.next_type_var += 1;
            (veri_ir::Expr::CLS(Box::new(e1)), t)
        }
        annotation_ir::Expr::A64CLS(ty, x) => {
            let (e0, t0) = add_annotation_constraints(*ty, tree, annotation_info);
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);

            let t = tree.next_type_var;
            tree.concrete_constraints.insert(TypeExpr::Concrete(
                t,
                annotation_ir::Type::BitVectorWithWidth(REG_WIDTH),
            ));
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t0, annotation_ir::Type::Int));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));

            tree.next_type_var += 1;
            (veri_ir::Expr::A64CLS(Box::new(e0), Box::new(e1)), t)
        }
        annotation_ir::Expr::Rev(x) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);

            let t = tree.next_type_var;
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));

            tree.next_type_var += 1;
            (veri_ir::Expr::Rev(Box::new(e1)), t)
        }
        annotation_ir::Expr::A64Rev(ty, x) => {
            let (e0, t0) = add_annotation_constraints(*ty, tree, annotation_info);
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);

            let t = tree.next_type_var;
            tree.concrete_constraints.insert(TypeExpr::Concrete(
                t,
                annotation_ir::Type::BitVectorWithWidth(REG_WIDTH),
            ));
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t0, annotation_ir::Type::Int));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));

            tree.next_type_var += 1;
            (veri_ir::Expr::A64Rev(Box::new(e0), Box::new(e1)), t)
        }
        annotation_ir::Expr::BVSubs(ty, x, y) => {
            let (e0, t0) = add_annotation_constraints(*ty, tree, annotation_info);
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);
            let (e2, t2) = add_annotation_constraints(*y, tree, annotation_info);

            let t = tree.next_type_var;

            // For aarch64, subs sets 4 flags. Model these as 4 bit appended to the left of the
            // register.
            tree.concrete_constraints.insert(TypeExpr::Concrete(
                t,
                annotation_ir::Type::BitVectorWithWidth(REG_WIDTH + FLAGS_WIDTH),
            ));
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t0, annotation_ir::Type::Int));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t2, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));

            tree.next_type_var += 1;
            (
                veri_ir::Expr::BVSubs(Box::new(e0), Box::new(e1), Box::new(e2)),
                t,
            )
        }
        annotation_ir::Expr::BVPopcnt(x) => {
            let (e1, t1) = add_annotation_constraints(*x, tree, annotation_info);

            let t = tree.next_type_var;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));

            tree.next_type_var += 1;
            (veri_ir::Expr::BVPopcnt(Box::new(e1)), t)
        }
    };
    tree.ty_vars.insert(e.clone(), t);
    (e, t)
}

fn add_isle_constraints(
    term: &sema::Term,
    tree: &mut RuleParseTree,
    annotation_env: &AnnotationEnv,
    annotation_info: &mut AnnotationTypeInfo,
    annotation: annotation_ir::TermSignature,
) {
    let mut annotation_vars = vec![];
    for a in annotation.args {
        annotation_vars.push(a.name);
    }
    annotation_vars.push(annotation.ret.name);

    let mut isle_types = vec![];
    for arg_ty in term.arg_tys.iter() {
        isle_types.push(arg_ty.clone());
    }
    isle_types.push(term.ret_ty.clone());
    assert_eq!(annotation_vars.len(), isle_types.len());

    for (isle_type_id, annotation_var) in isle_types.iter().zip(annotation_vars) {
        // in case the var was not in the annotation
        if !annotation_info
            .var_to_type_var
            .contains_key(&annotation_var)
        {
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;

            annotation_info
                .var_to_type_var
                .insert(annotation_var.clone(), type_var);
        }

        if let Some(ir_type) = annotation_env.model_map.get(isle_type_id) {
            let type_var = annotation_info.var_to_type_var[&annotation_var];
            match ir_type {
                annotation_ir::Type::BitVector => tree
                    .bv_constraints
                    .insert(TypeExpr::Concrete(type_var, ir_type.clone())),
                _ => tree
                    .concrete_constraints
                    .insert(TypeExpr::Concrete(type_var, ir_type.clone())),
            };
        }
    }
}

fn add_rule_constraints(
    tree: &mut RuleParseTree,
    curr: &mut TypeVarNode,
    termenv: &TermEnv,
    typeenv: &TypeEnv,
    annotation_env: &AnnotationEnv,
    annotation_infos: &mut Vec<AnnotationTypeInfo>,
    rhs: bool,
) -> Option<veri_ir::Expr> {
    // Only relate args to annotations for terms. For leaves, return immediately.
    // For recursive definitions without annotations (like And and Let), recur.
    let mut children = vec![];
    for child in &mut curr.children {
        if let Some(e) = add_rule_constraints(
            tree,
            child,
            termenv,
            typeenv,
            annotation_env,
            annotation_infos,
            rhs,
        ) {
            children.push(e);
        } else {
            return None;
        }
    }
    let e = match &curr.construct {
        TypeVarConstruct::Var => {
            tree.quantified_vars
                .insert(curr.ident.clone(), curr.type_var);
            tree.free_vars.insert(curr.ident.clone(), curr.type_var);
            Some(veri_ir::Expr::Terminal(veri_ir::Terminal::Var(
                curr.ident.clone(),
            )))
        }
        TypeVarConstruct::BindPattern => {
            assert_eq!(children.len(), 2);
            tree.assumptions.push(veri_ir::Expr::Binary(
                veri_ir::BinaryOp::Eq,
                Box::new(children[0].clone()),
                Box::new(children[1].clone()),
            ));
            Some(children[0].clone())
        }
        TypeVarConstruct::Wildcard(i) => {
            Some(veri_ir::Expr::Terminal(veri_ir::Terminal::Wildcard(*i)))
        }
        TypeVarConstruct::Const(i) => {
            // If constant is known, add the value to the tree. Useful for
            // capturing isleTypes
            tree.type_var_to_val_map.insert(curr.type_var, *i);

            Some(veri_ir::Expr::Terminal(veri_ir::Terminal::Const(
                *i,
                curr.type_var,
            )))
        }
        TypeVarConstruct::And => {
            tree.quantified_vars
                .insert(curr.ident.clone(), curr.type_var);
            let first = &children[0];
            for (i, e) in children.iter().enumerate() {
                if i != 0 {
                    tree.assumptions.push(veri_ir::Expr::Binary(
                        veri_ir::BinaryOp::Eq,
                        Box::new(first.clone()),
                        Box::new(e.clone()),
                    ))
                }
            }
            Some(first.to_owned())
        }
        TypeVarConstruct::Let(bound) => {
            tree.quantified_vars
                .insert(curr.ident.clone(), curr.type_var);
            for (e, s) in children.iter().zip(bound) {
                tree.assumptions.push(veri_ir::Expr::Binary(
                    veri_ir::BinaryOp::Eq,
                    Box::new(veri_ir::Expr::Terminal(veri_ir::Terminal::Var(
                        s.to_owned(),
                    ))),
                    Box::new(e.to_owned()),
                ))
            }
            children.last().cloned()
        }
        TypeVarConstruct::Term(term_id) => {
            let term = &termenv.terms[term_id.index()];
            let term_name = typeenv.syms[term.name.index()].clone();

            // Print term for debugging
            print!(" {}", term_name);

            tree.quantified_vars
                .insert(curr.ident.clone(), curr.type_var);
            let a = annotation_env.get_annotation_for_term(term_id);
            if a.is_none() {
                println!("\nSkipping rule with unannotated term: {}", term_name);
                return None;
            }
            let annotation = a.unwrap();

            // use a fresh mapping for each term
            // keep the same mapping between assertions in the same annotation
            let mut annotation_info = AnnotationTypeInfo {
                term: curr.ident.clone(),
                var_to_type_var: HashMap::new(),
            };
            for expr in annotation.assumptions {
                let (typed_expr, _) = add_annotation_constraints(*expr, tree, &mut annotation_info);
                curr.assertions.push(typed_expr.clone());
                tree.assumptions.push(typed_expr);
                add_isle_constraints(
                    term,
                    tree,
                    annotation_env,
                    &mut annotation_info,
                    annotation.sig.clone(),
                );
            }
            // For assertions, global assume if not RHS, otherwise assert
            for expr in annotation.assertions {
                let (typed_expr, _) = add_annotation_constraints(*expr, tree, &mut annotation_info);
                curr.assertions.push(typed_expr.clone());
                add_isle_constraints(
                    term,
                    tree,
                    annotation_env,
                    &mut annotation_info,
                    annotation.sig.clone(),
                );
                if rhs {
                    tree.rhs_assertions.push(typed_expr);
                } else {
                    tree.assumptions.push(typed_expr);
                }
            }

            // set args in rule equal to args in annotation
            for (child, arg) in curr.children.iter().zip(&annotation.sig.args) {
                let rule_type_var = child.type_var;
                let annotation_type_var = annotation_info.var_to_type_var[&arg.name];

                // essentially constant propagate: if we know the value from the rule arg being
                // provided as a literal, propagate this to the annotation.
                if let Some(c) = tree.type_var_to_val_map.get(&rule_type_var) {
                    tree.type_var_to_val_map.insert(annotation_type_var, *c);
                }
                tree.var_constraints
                    .insert(TypeExpr::Variable(rule_type_var, annotation_type_var));
            }

            for (child, arg) in children.iter().zip(&annotation.sig.args) {
                let annotation_type_var = annotation_info.var_to_type_var[&arg.name];
                let arg_name = format!(
                    "{}__{}__{}",
                    annotation_info.term, arg.name, annotation_type_var
                );
                tree.quantified_vars
                    .insert(arg_name.clone(), annotation_type_var);
                tree.assumptions.push(veri_ir::Expr::Binary(
                    veri_ir::BinaryOp::Eq,
                    Box::new(child.clone()),
                    Box::new(veri_ir::Expr::Terminal(veri_ir::Terminal::Var(arg_name))),
                ))
            }
            // set term ret var equal to annotation ret var
            let ret_var = annotation_info.var_to_type_var[&annotation.sig.ret.name];
            tree.var_constraints
                .insert(TypeExpr::Variable(curr.type_var, ret_var));
            let ret_name = format!(
                "{}__{}__{}",
                annotation_info.term, annotation.sig.ret.name, ret_var
            );
            tree.quantified_vars.insert(ret_name.clone(), ret_var);
            tree.assumptions.push(veri_ir::Expr::Binary(
                veri_ir::BinaryOp::Eq,
                Box::new(veri_ir::Expr::Terminal(veri_ir::Terminal::Var(
                    curr.ident.clone(),
                ))),
                Box::new(veri_ir::Expr::Terminal(veri_ir::Terminal::Var(ret_name))),
            ));

            annotation_infos.push(annotation_info);

            Some(veri_ir::Expr::Terminal(veri_ir::Terminal::Var(
                curr.ident.clone(),
            )))
        }
    };
    if let Some(e) = e {
        tree.ty_vars.insert(e.clone(), curr.type_var);
        Some(e)
    } else {
        None
    }
}

fn solve_constraints(
    concrete: &HashSet<TypeExpr>,
    var: &HashSet<TypeExpr>,
    bv: &HashSet<TypeExpr>,
    vals: &mut HashMap<u32, i128>,
    _lhs_expr: &Expr,
    _rhs_expr: &Expr,
    //ty_vars: Option<&HashMap<veri_ir::Expr, u32>>,
) -> (HashMap<u32, annotation_ir::Type>, HashMap<u32, u32>) {
    // Setup
    let smt = easy_smt::ContextBuilder::new()
        .replay_file(Some(std::fs::File::create("type_solver.smt2").unwrap()))
        .solver("z3", ["-smt2", "-in"])
        .build()
        .unwrap();

    let mut solver = TypeSolver::new(smt);
    solver.add_constraints(concrete);
    solver.add_constraints(var);
    solver.add_constraints(bv);
    solver.set_values(vals);

    let result = solver.solve();

    let bv_unknown_width_sets = HashMap::new();
    (result, bv_unknown_width_sets)
}

struct TypeSolver {
    smt: easy_smt::Context,

    // Symbolic type for each type variable.
    symbolic_types: HashMap<u32, SymbolicType>,
}

impl TypeSolver {
    fn new(smt: easy_smt::Context) -> Self {
        Self {
            smt,
            symbolic_types: HashMap::new(),
        }
    }

    fn solve(&mut self) -> HashMap<u32, annotation_ir::Type> {
        let response = self.smt.check().unwrap();
        assert_eq!(response, Response::Sat);

        let vs: Vec<_> = self.symbolic_types.keys().copied().collect();
        let mut tys = HashMap::new();
        for v in vs {
            tys.insert(v, self.get_type(v));
        }
        tys
    }

    fn get_type(&mut self, v: u32) -> annotation_ir::Type {
        let symbolic_type = self.get_symbolic_type(v);

        // Lookup discriminant from the model.
        let discriminant_value =
            usize::try_from(self.get_value_data(symbolic_type.discriminant.expr))
                .expect("discriminant value should be integer");
        let discriminant =
            TypeDiscriminant::from_repr(discriminant_value).expect("unknown discriminant value");

        match discriminant {
            TypeDiscriminant::BitVector => {
                // Is the bitvector width known?
                let has_width = self.get_bool_value(symbolic_type.bitvector_width.some.expr);
                if !has_width {
                    return annotation_ir::Type::BitVector;
                }

                // Lookup width.
                let width =
                    usize::try_from(self.get_value_data(symbolic_type.bitvector_width.value.expr))
                        .expect("bitvector width should be integer");

                annotation_ir::Type::BitVectorWithWidth(width)
            }
            TypeDiscriminant::Bool => annotation_ir::Type::Bool,
            TypeDiscriminant::Int => annotation_ir::Type::Int,
        }
    }

    fn get_bool_value(&mut self, expr: SExpr) -> bool {
        let value = self.get_value(expr);
        if value == self.smt.true_() {
            true
        } else if value == self.smt.false_() {
            false
        } else {
            unreachable!("value is not boolean");
        }
    }

    fn get_value_data(&mut self, expr: SExpr) -> SExprData {
        let value = self.get_value(expr);
        self.smt.get(value)
    }

    fn get_value(&mut self, expr: SExpr) -> SExpr {
        let values = self.smt.get_value(vec![expr]).unwrap();
        assert_eq!(values.len(), 1);
        values[0].1
    }

    fn add_constraints(&mut self, type_exprs: &HashSet<TypeExpr>) {
        for type_expr in type_exprs {
            self.add_constraint(type_expr);
        }
    }

    fn add_constraint(&mut self, type_expr: &TypeExpr) {
        match type_expr {
            TypeExpr::Concrete(v, ty) => self.concrete(*v, ty),
            TypeExpr::Variable(u, v) => self.variable(*u, *v),
            TypeExpr::WidthInt(v, w) => self.width_int(*v, *w),
            TypeExpr::Symbolic(l, r) => self.symbolic_sum(l.clone(), r.clone()),
        }
    }

    fn set_values(&mut self, vals: &HashMap<u32, i128>) {
        for (v, n) in vals {
            self.set_value(*v, *n);
        }
    }

    fn set_value(&mut self, v: u32, n: i128) {
        // If it's an integer, it should have this value.
        let symbolic_type = self.get_symbolic_type(v);
        self.smt
            .assert(
                self.smt.imp(
                    self.smt.eq(
                        symbolic_type.discriminant.expr,
                        self.smt.numeral(TypeDiscriminant::Int as u8),
                    ),
                    self.smt.and(
                        symbolic_type.integer_value.some.expr,
                        self.smt
                            .eq(symbolic_type.integer_value.value.expr, self.smt.numeral(n)),
                    ),
                ),
            )
            .unwrap();
    }

    fn concrete(&mut self, v: u32, ty: &annotation_ir::Type) {
        let symbolic_type = self.get_symbolic_type(v);
        match ty {
            annotation_ir::Type::BitVector => {
                self.assert_type_discriminant(&symbolic_type, TypeDiscriminant::BitVector);
            }
            annotation_ir::Type::BitVectorWithWidth(w) => {
                self.assert_type_discriminant(&symbolic_type, TypeDiscriminant::BitVector);
                self.assert_option_value(&symbolic_type.bitvector_width, self.smt.numeral(*w));
            }
            annotation_ir::Type::Int => {
                self.assert_type_discriminant(&symbolic_type, TypeDiscriminant::Int)
            }
            annotation_ir::Type::Bool => {
                self.assert_type_discriminant(&symbolic_type, TypeDiscriminant::Bool)
            }
            _ => todo!("concrete: {ty:?}"),
        }
    }

    fn variable(&mut self, u: u32, v: u32) {
        let a = self.get_symbolic_type(u);
        let b = self.get_symbolic_type(v);
        self.assert_types_equal(&a, &b);
    }

    fn width_int(&mut self, v: u32, w: u32) {
        // Type v is a bitvector, type w is an integer, and the bitwidth of v is
        // equal to the value of w.
        let bitvector_type = self.get_symbolic_type(v);
        let width_type = self.get_symbolic_type(w);

        self.assert_type_discriminant(&bitvector_type, TypeDiscriminant::BitVector);
        self.assert_type_discriminant(&width_type, TypeDiscriminant::Int);
        self.assert_options_equal(&bitvector_type.bitvector_width, &width_type.integer_value)
    }

    fn symbolic_sum(&mut self, l: Vec<u32>, r: Vec<u32>) {
        // get the expressions of each bv we want to add
        let l_widths: Vec<SExpr> = l
            .iter()
            .map(|s| self.get_symbolic_type(*s).bitvector_width.value.expr)
            .collect();
        // sum them together
        let l_sum = self.smt.plus_many(l_widths);

        // same for rhs
        let r_widths: Vec<SExpr> = r
            .iter()
            .map(|s| self.get_symbolic_type(*s).bitvector_width.value.expr)
            .collect();
        let r_sum = self.smt.plus_many(r_widths);
        self.smt.assert(self.smt.eq(l_sum, r_sum)).unwrap();
    }

    fn assert_type_discriminant(&mut self, symbolic_type: &SymbolicType, disc: TypeDiscriminant) {
        let disc = self.smt.numeral(disc as u8);
        let eq = self.smt.eq(symbolic_type.discriminant.expr, disc);
        self.smt.assert(eq).unwrap();
    }

    fn assert_option_value(&mut self, symbolic_option: &SymbolicOption, value: SExpr) {
        self.smt.assert(symbolic_option.some.expr).unwrap();
        self.smt
            .assert(self.smt.eq(symbolic_option.value.expr, value))
            .unwrap();
    }

    fn assert_types_equal(&mut self, a: &SymbolicType, b: &SymbolicType) {
        // Note that we assert nothing about the integer value, only that the
        // types are the same.
        self.assert_variables_equal(&a.discriminant, &b.discriminant);
        self.assert_options_equal(&a.bitvector_width, &b.bitvector_width);
    }

    fn assert_options_equal(&mut self, a: &SymbolicOption, b: &SymbolicOption) {
        self.assert_variables_equal(&a.some, &b.some);
        self.assert_variables_equal(&a.value, &b.value);
    }

    fn assert_variables_equal(&mut self, a: &SymbolicVariable, b: &SymbolicVariable) {
        self.smt.assert(self.smt.eq(a.expr, b.expr)).unwrap();
    }

    fn get_symbolic_type(&mut self, v: u32) -> SymbolicType {
        self.symbolic_types
            .entry(v)
            .or_insert_with(|| SymbolicType::decl(&mut self.smt, v))
            .clone()
    }
    fn display_isle_pattern(
        &mut self,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        rule: &sema::Rule,
        annotation_infos: &Vec<AnnotationTypeInfo>,
        type_sols: &HashMap<u32, veri_ir::annotation_ir::Type>,
        pat: &Pattern,
        parent_term: Option<&AnnotationTypeInfo>,
    ) -> SExpr {
        let mut to_sexpr =
            |ai, p, pt| self.display_isle_pattern(termenv, typeenv, rule, ai, type_sols, p, pt);

        let mut anno = annotation_infos.clone();
        match pat {
            sema::Pattern::Term(_, term_id, args) => {
                let sym = termenv.terms[term_id.index()].name;
                let name = typeenv.syms[sym.index()].clone();

                let matches: Vec<&AnnotationTypeInfo> = annotation_infos
                    .iter()
                    .filter(|t| t.term.starts_with(&name))
                    .collect();

                let mut var = " ".to_string();
                if matches.len() == 0 {
                    println!("Can't find match for: {}", name);
                    panic!();
                } else if matches.len() >= 1 {
                    var = format!(
                        "[{}|{}]",
                        type_to_num(
                            type_sols
                                .get(
                                    &matches
                                        .first()
                                        .unwrap()
                                        .var_to_type_var
                                        .get("result")
                                        .unwrap()
                                )
                                .unwrap()
                        ),
                        name
                    );
                    if matches.len() > 1 {
                        let index = annotation_infos
                            .iter()
                            .position(|t| t.term == matches.first().unwrap().term)
                            .unwrap();
                        anno.remove(index);
                    }
                }

                let mut sexprs: Vec<SExpr> = args
                    .iter()
                    .map(|a| to_sexpr(&anno, a, matches.first().copied()))
                    .collect::<Vec<SExpr>>();

                sexprs.insert(0, self.smt.atom(var));
                self.smt.list(sexprs)
            }

            sema::Pattern::Var(_, var_id) => {
                let sym = rule.vars[var_id.index()].name;
                let ident = typeenv.syms[sym.index()].clone();

                let mut var = " ".to_string();
                match parent_term {
                    Some(value) => {
                        var = format!(
                            "[{}|{}]",
                            type_to_num(
                                type_sols
                                    .get(&value.var_to_type_var.get(&ident).unwrap())
                                    .unwrap()
                            ),
                            ident
                        );
                    }
                    None => print!("Not found!"),
                }

                self.smt.atom(var)
            }
            sema::Pattern::BindPattern(_, var_id, subpat) => {
                let sym = rule.vars[var_id.index()].name;
                let ident = &typeenv.syms[sym.index()];
                let subpat_node = to_sexpr(annotation_infos, subpat, parent_term);

                let mut var = " ".to_string();
                match parent_term {
                    Some(value) => match value.var_to_type_var.get(ident) {
                        Some(ty) => {
                            var =
                                format!("[{}|{}]", type_to_num(type_sols.get(ty).unwrap()), ident);
                        }
                        None => {
                            var = format!(
                                "[{}|{}]",
                                type_to_num(
                                    type_sols
                                        .get(&value.var_to_type_var.get("arg").unwrap())
                                        .unwrap()
                                ),
                                ident
                            );
                        }
                    },
                    None => print!("Not found!"),
                }
                // Special case: elide bind patterns to wildcars
                if matches!(**subpat, sema::Pattern::Wildcard(_)) {
                    self.smt.atom(&var)
                } else {
                    self.smt
                        .list(vec![self.smt.atom(&var), self.smt.atom("@"), subpat_node])
                }
            }
            sema::Pattern::Wildcard(_) => self.smt.list(vec![self.smt.atom("_")]),
            sema::Pattern::ConstPrim(_, sym) => {
                let name = typeenv.syms[sym.index()].clone();
                self.smt.list(vec![self.smt.atom(name)])
            }
            sema::Pattern::ConstInt(_, num) => {
                let _smt_name_prefix = format!("{}__", num);
                // TODO: look up BV vs int
                self.smt.list(vec![self.smt.atom(num.to_string())])
            }
            sema::Pattern::And(_, subpats) => {
                let mut sexprs = subpats
                    .iter()
                    .map(|a| to_sexpr(annotation_infos, a, parent_term))
                    .collect::<Vec<SExpr>>();

                sexprs.insert(0, self.smt.atom("and"));
                self.smt.list(sexprs)
            }
        }
    }
    fn display_isle_expr(
        &self,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        rule: &sema::Rule,
        annotation_infos: &Vec<AnnotationTypeInfo>,
        type_sols: &HashMap<u32, veri_ir::annotation_ir::Type>,
        expr: &sema::Expr,
        parent_term: Option<&AnnotationTypeInfo>,
    ) -> SExpr {
        let to_sexpr =
            |ai, e, pt| self.display_isle_expr(termenv, typeenv, rule, ai, type_sols, e, pt);

        let mut anno = annotation_infos.clone();

        match expr {
            sema::Expr::Term(_, term_id, args) => {
                let sym = termenv.terms[term_id.index()].name;
                let name = typeenv.syms[sym.index()].clone();

                let matches: Vec<&AnnotationTypeInfo> = annotation_infos
                    .iter()
                    .filter(|t| t.term.starts_with(&name))
                    .collect();

                let mut var = " ".to_string();
                if matches.len() == 0 {
                    println!("Can't find match for: {}", name);
                    panic!();
                } else if matches.len() >= 1 {
                    var = format!(
                        "[{}|{}]",
                        type_to_num(
                            type_sols
                                .get(
                                    &matches
                                        .first()
                                        .unwrap()
                                        .var_to_type_var
                                        .get("result")
                                        .unwrap()
                                )
                                .unwrap()
                        ),
                        name
                    );
                    if matches.len() > 1 {
                        let index = annotation_infos
                            .iter()
                            .position(|t| t.term == matches.first().unwrap().term)
                            .unwrap();
                        anno.remove(index);
                    }
                }

                let mut sexprs = args
                    .iter()
                    .map(|a| to_sexpr(&anno, a, matches.first().copied()))
                    .collect::<Vec<SExpr>>();
                sexprs.insert(0, self.smt.atom(var));
                self.smt.list(sexprs)
            }
            sema::Expr::Var(_, var_id) => {
                let sym = rule.vars[var_id.index()].name;
                let ident = typeenv.syms[sym.index()].clone();

                let mut var = " ".to_string();
                match parent_term {
                    Some(value) => match value.var_to_type_var.get(&ident) {
                        Some(ty) => {
                            var =
                                format!("[{}|{}]", type_to_num(type_sols.get(ty).unwrap()), ident);
                        }
                        None => {
                            var = format!(
                                "[{}|{}]",
                                type_to_num(
                                    type_sols
                                        .get(&value.var_to_type_var.get("arg").unwrap())
                                        .unwrap()
                                ),
                                ident
                            );
                        }
                    },
                    None => print!("Not found!"),
                }

                self.smt.atom(var)
            }
            sema::Expr::ConstPrim(_, sym) => {
                let name = typeenv.syms[sym.index()].clone();
                self.smt.list(vec![self.smt.atom(name)])
            }
            sema::Expr::ConstInt(_, num) => {
                let _smt_name_prefix = format!("{}__", num);
                // TODO: look up BV vs int
                self.smt.list(vec![self.smt.atom(num.to_string())])
            }
            sema::Expr::Let { bindings, body, .. } => {
                let mut sexprs = vec![];
                for (varid, _, expr) in bindings {
                    let sym = rule.vars[varid.index()].name;
                    let ident = typeenv.syms[sym.index()].clone();

                    sexprs.push(self.smt.list(vec![
                        self.smt.atom(ident),
                        to_sexpr(annotation_infos, expr, parent_term),
                    ]));
                }
                self.smt.list(vec![
                    self.smt.atom("let"),
                    self.smt.list(sexprs),
                    to_sexpr(annotation_infos, body, parent_term),
                ])
            }
        }
    }
}

#[derive(Clone)]
struct SymbolicVariable {
    name: String,
    expr: SExpr,
}

impl SymbolicVariable {
    fn integer(smt: &mut easy_smt::Context, name: String) -> Self {
        Self::decl_sort(smt, name, smt.int_sort())
    }

    fn boolean(smt: &mut easy_smt::Context, name: String) -> Self {
        Self::decl_sort(smt, name, smt.bool_sort())
    }

    fn decl_sort(smt: &mut easy_smt::Context, name: String, sort: SExpr) -> Self {
        smt.declare_const(name.clone(), sort).unwrap();
        let expr = smt.atom(name.clone());
        Self { name, expr }
    }
}

#[derive(Clone)]
struct SymbolicOption {
    some: SymbolicVariable,
    value: SymbolicVariable,
}

impl SymbolicOption {
    fn decl(smt: &mut easy_smt::Context, value: SymbolicVariable) -> Self {
        let some = SymbolicVariable::boolean(smt, format!("{}_some", value.name));
        Self { some, value }
    }
}

#[derive(EnumIter, FromRepr, Debug)]
enum TypeDiscriminant {
    BitVector = 1,
    Int = 2,
    Bool = 3,
}

#[derive(Clone)]
struct SymbolicType {
    discriminant: SymbolicVariable,
    bitvector_width: SymbolicOption,
    integer_value: SymbolicOption,
}

impl SymbolicType {
    fn decl(smt: &mut easy_smt::Context, v: u32) -> Self {
        let prefix = format!("t{}", v);

        // Disciminant.
        let discriminant = SymbolicVariable::integer(smt, format!("{prefix}_disc"));

        // Invariant: discriminant is one of the allowed values
        smt.assert(smt.or_many(
            TypeDiscriminant::iter().map(|d| smt.eq(discriminant.expr, smt.numeral(d as u8))),
        ))
        .unwrap();

        // Bitvector width (option).
        let bitvector_width_value =
            SymbolicVariable::integer(smt, format!("{prefix}_bitvector_width"));
        let bitvector_width = SymbolicOption::decl(smt, bitvector_width_value);

        // Invariant: if not bitvector then bitvector width option is none.
        smt.assert(smt.imp(
            smt.distinct(
                discriminant.expr,
                smt.numeral(TypeDiscriminant::BitVector as u8),
            ),
            smt.not(bitvector_width.some.expr),
        ))
        .unwrap();

        // Invariant: if bitvector width option is none, then its value is 0.
        smt.assert(smt.imp(
            smt.not(bitvector_width.some.expr),
            smt.eq(bitvector_width.value.expr, smt.numeral(0)),
        ))
        .unwrap();

        // Integer value.
        let integer_value_value = SymbolicVariable::integer(smt, format!("{prefix}_integer_value"));
        let integer_value = SymbolicOption::decl(smt, integer_value_value);

        // Invariant: if not integer then integer value option is none.
        smt.assert(smt.imp(
            smt.distinct(discriminant.expr, smt.numeral(TypeDiscriminant::Int as u8)),
            smt.not(integer_value.some.expr),
        ))
        .unwrap();

        // Invariant: if integer value option is none, then its value is 0.
        smt.assert(smt.imp(
            smt.not(integer_value.some.expr),
            smt.eq(integer_value.value.expr, smt.numeral(0)),
        ))
        .unwrap();

        Self {
            discriminant,
            bitvector_width,
            integer_value,
        }
    }
}

fn main() {
    let args = Args::parse();
    let mut inputs = vec![];

    let cur_dir = env::current_dir().expect("Can't access current working directory");
    if !args.noprelude {
        // Build the relevant ISLE prelude using the meta crate
        inputs.push(build_clif_lower_isle());

        // TODO: clean up path logic
        inputs.push(cur_dir.join("./ref").join("inst_specs.isle"));
        inputs.push(cur_dir.join("./ref").join("prelude.isle"));
        inputs.push(cur_dir.join("./ref").join("prelude_lower.isle"));
    }

    // DO NOT include these for broken tests
    if args.aarch64 {
        inputs.push(cur_dir.join("./ref/aarch64").join("inst.isle"));
        inputs.push(cur_dir.join("./ref/aarch64").join("inst_specs.isle"));
        inputs.push(cur_dir.join("./ref/aarch64").join("lower.isle"));
    }

    if let Some(i) = args.input {
        inputs.push(PathBuf::from(i));
    } else {
        panic!("Missing input file in non-aarch64 mode");
    }

    // Parse AST.
    let ast = parse(Lexer::from_files(&inputs).unwrap()).expect("should parse");
    // dbg!(&ast);
    // Type Environment
    let mut tyenv = TypeEnv::from_ast(&ast).expect("should not have type-definition errors");
    // dbg!(&tyenv);
    // Term Environment
    let termenv: TermEnv =
        TermEnv::from_ast(&mut tyenv, &ast, false).expect("should not have type-definition errors");
    // dbg!(&termenv);

    let annotation_env = parse_annotations(&ast, &termenv, &tyenv);

    // let mut rule_names = ast
    //     .defs
    //     .iter()
    //     .filter_map(|x| {
    //         if let Def::Rule(value) = x {
    //             Some(&value.name)
    //         } else {
    //             None
    //         }
    //     })
    //     .map(|x| x.clone().expect("Isn't Ident").0.to_owned())
    //     .collect::<Vec<_>>();
    // rule_names.dedup();

    let names = if let Some(names) = args.names {
        let mut names = names;
        names.sort();
        names.dedup();
        Some(names)
    } else {
        None
    };

    let config = Config {
        term: args.term,
        names: names,
    };

    // Get the types/widths for this particular term
    let types = annotation_env
        .get_term_signatures_by_name(&termenv, &tyenv)
        .get(&config.term as &str)
        .expect(format!("Missing term width for {}", config.term).as_str())
        .clone();

    for type_instantiation in types {
        let _type_sols = type_rules_with_term_and_types(
            &termenv,
            &tyenv,
            &annotation_env,
            &config,
            &type_instantiation,
            &None,
        );

        // Old print method:
        //     for rules in &type_sols {
        //         for annotation in &rules.1.annotation_infos {
        //             println!("\nTyping Rule for {}", annotation.term);
        //             for var in &annotation.var_to_type_var {
        //                 println!(
        //                     "{}: {:?}",
        //                     var.0,
        //                     rules.1.type_var_to_type.get(var.1).unwrap()
        //                 );
        //             }
        //         }
        //     }
    }
}
