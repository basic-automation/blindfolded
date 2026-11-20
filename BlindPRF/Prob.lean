/-
  BlindPRF/Prob.lean — a small, self-contained toolkit for uniform distributions on finite types.

  Mathlib's `PMF` monad (`PMF.pure`, `PMF.bind`, `PMF.map`) is used as the probability language.
  The uniform distribution is defined here directly from `PMF.ofFintype` so that the development
  does not depend on the (currently migrating) named-distribution API in Mathlib.
-/
import Mathlib

namespace BlindPRF

open scoped ENNReal

universe u v w

/-- The uniform distribution on a nonempty finite type: every element has mass `1 / |α|`. -/
noncomputable def unif (α : Type u) [Fintype α] [Nonempty α] : PMF α :=
  PMF.ofFintype (fun _ => (Fintype.card α : ℝ≥0∞)⁻¹) (by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _))

section

variable {α : Type u} {β : Type v} {γ : Type w}

@[simp]
theorem unif_apply [Fintype α] [Nonempty α] (a : α) :
    unif α a = (Fintype.card α : ℝ≥0∞)⁻¹ := rfl

/-- **Bijection rule.** Pushing the uniform distribution forward along a bijection gives the
uniform distribution. -/
theorem unif_map_equiv [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β) :
    (unif α).map e = unif β := by
  ext b
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp [Fintype.card_congr e]
  · intro a ha
    have : b ≠ e a := fun h => ha (by simp [h])
    simp [this]

/-- A relabelling of the sample space by a bijection does not change the distribution of any
quantity computed from the sample ("optimistic sampling" / "random-variable swap"). -/
theorem unif_map_eq_of_equiv [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) (f : α → γ) (g : β → γ) (h : ∀ a, g (e a) = f a) :
    (unif α).map f = (unif β).map g := by
  have hf : f = g ∘ e := by funext a; simp [h a]
  rw [hf, ← PMF.map_comp, unif_map_equiv]

/-- Same as `unif_map_eq_of_equiv`, for an experiment that continues probabilistically. -/
theorem unif_bind_eq_of_equiv [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) (f : α → PMF γ) (g : β → PMF γ) (h : ∀ a, g (e a) = f a) :
    (unif α).bind f = (unif β).bind g := by
  have hf : f = g ∘ e := by funext a; simp [h a]
  rw [hf, ← PMF.bind_map, unif_map_equiv]

/-- The uniform distribution on a product is the product of the uniform distributions. -/
theorem unif_prod [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    unif (α × β) = (unif α).bind fun a => (unif β).map fun b => (a, b) := by
  classical
  ext ⟨a, b⟩
  rw [PMF.bind_apply, tsum_eq_single a]
  · rw [PMF.map_apply, tsum_eq_single b]
    · simp [Fintype.card_prod, ENNReal.mul_inv]
    · intro b' hb'
      have : (a, b) ≠ (a, b') := fun h => hb' (by simpa using h.symm)
      simp [this]
  · intro a' ha'
    have : ∀ b', (a, b) ≠ (a', b') := fun b' h => ha' (by simpa using (congrArg Prod.fst h).symm)
    simp [PMF.map_apply, this]

/-- Sampling a pair uniformly is the same as sampling the two components independently. -/
theorem unif_prod_bind [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (f : α × β → PMF γ) :
    (unif (α × β)).bind f = (unif α).bind fun a => (unif β).bind fun b => f (a, b) := by
  rw [unif_prod, PMF.bind_bind]
  congr 1
  funext a
  rw [PMF.bind_map]
  rfl

/-- Marginal of a uniform pair: the first component is uniform. -/
theorem unif_map_fst [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    (unif (α × β)).map Prod.fst = unif α := by
  rw [unif_prod, PMF.map_bind]
  have : (fun a : α => ((unif β).map fun b => (a, b)).map Prod.fst) = fun a => PMF.pure a := by
    funext a
    rw [PMF.map_comp]
    exact PMF.map_const _ _
  rw [this, PMF.bind_pure]

/-- Marginal of a uniform pair: the second component is uniform. -/
theorem unif_map_snd [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    (unif (α × β)).map Prod.snd = unif β := by
  have h := unif_map_eq_of_equiv (Equiv.prodComm α β) (Prod.snd : α × β → β)
    (Prod.fst : β × α → β) (by intro a; rfl)
  rw [h, unif_map_fst]

/-- A sample that the continuation ignores can be dropped. -/
theorem unif_bind_const [Fintype α] [Nonempty α] (q : PMF γ) :
    ((unif α).bind fun _ => q) = q :=
  PMF.bind_const _ _

/-- **Fibre rule.** If `π : α → β` factors as a bijection `α ≃ β × κ` followed by the first
projection (i.e. all fibres of `π` have the same size), then `π` pushes the uniform distribution
on `α` to the uniform distribution on `β`. -/
theorem unif_map_of_equiv_prod {κ : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [Fintype κ] [Nonempty κ] (e : α ≃ β × κ) (π : α → β) (h : ∀ a, (e a).1 = π a) :
    (unif α).map π = unif β := by
  rw [unif_map_eq_of_equiv e π Prod.fst h, unif_map_fst]

end

end BlindPRF
