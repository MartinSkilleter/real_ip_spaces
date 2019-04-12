import analysis.normed_space.basic
import data.complex.basic

class has_inner_product (α : Type*) := (inner_product : α → α → ℂ)

class inner_product_space (α : Type*) extends has_inner_product α, add_comm_group α, vector_space ℂ α

