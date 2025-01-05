mod chap1;
mod finite_field;
mod poly;
mod utils;

fn main() {
    println!("Hello world!");
    println!("{}", chap1::kronecker_symbol(23, 59));
}
