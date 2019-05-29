import inner_product_spaces.real_ip.orthonormal_bases

variables {α : Type*}

variables [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]

variables [Hilbert_space α]
variables {S : @submodule ℝ α _ _ _}
variables {h : @is_closed α (α_topological_space) S.carrier}

open real set submodule

include h

local attribute [instance] classical.prop_decidable

variables {f : α →ₗ[ℝ] ℝ}

