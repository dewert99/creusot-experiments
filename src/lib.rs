#![allow(unused)]
#![allow(path_statements)]
#![feature(unboxed_closures)]
#![cfg_attr(not(feature = "contracts"), feature(proc_macro_hygiene, stmt_expr_attributes))]
extern crate core;

//extern crate core;
//mod iterators;
//mod fail;
// mod transmute;
// mod uninit;
// mod boxed;
mod ghost_ptr;
// mod linked_list;
mod helpers;
mod p_map;
mod graph;
//mod seq_helpers;
