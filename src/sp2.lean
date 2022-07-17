import algebra.big_operators
import data.finset.slice
import data.rat
import tactic

open finset nat
open_locale big_operators 

namespace finset
namespace bbsetpair2
--Bollobas set pair theorem 
--A and B are the families of finite sets indexed by I
--sp is the condition the family satisfies
--spi is a shortcut for disjoint-ness  of A i and B i 
--U is the universe of elements in any of the sets 
-- it has size u
@[ext] structure setpair :=
  (A : ℕ → finset ℕ) (B : ℕ → finset ℕ) (I : finset ℕ)
  (sp : ∀i∈ I,∀j∈ I, ((A i)∩(B j)).nonempty ↔ i ≠ j)
  (spi : ∀i∈ I, disjoint (A i) (B i))
  (U : finset ℕ) (Ug : U = I.bUnion(λ i, (A i) ∪ (B i )))
  (u : ℕ) (ug: u= card U)
 --- we take the trivial system with I=∅  
instance  : inhabited setpair :={
default:= {A:=λ _,∅, B:=λ _,∅,I:=∅, 
sp:=begin tauto, end,
spi:=begin tauto, end,
U:=∅, Ug:=begin tauto, end,
u:=0, ug:=begin tauto,end,}}
-- density of a setpair system
@[simp]def den (S : setpair) :ℚ := ∑ i in S.I, ((1 : ℚ)/(card(S.A i)+card(S.B i)).choose (card (S.B i)))
-- helper - if A i and B j are disjoint then i=j
lemma sp' {S : setpair} {i j : ℕ}: i∈ S.I → j∈S.I → (disjoint (S.A i) (S.B j) → i = j):=
begin
  intros hi hj hd, 
  by_contra,
  have ne: ((S.A i)∩(S.B j)).nonempty,
    apply (S.sp i hi j hj).mpr h,
    rw disjoint_iff_inter_eq_empty at hd, 
    simp only [ * , not_nonempty_empty] at *,
end

-- the erase constructor - gives a new setpair without element x
-- we discard all i such that B i contains x and then erase x from any A i containing x
@[simp]def er  (S : setpair) (x : ℕ) : setpair :={
  A:=λ  n, erase (S.A n) x,
  B:=S.B,
  I:=S.I.filter(λi, x∉(S.B i)),
  sp:=begin
    intros i  hi j  hj,
    rw [mem_filter] at *,
    suffices same: ((S.A i).erase x ∩ S.B j) = (S.A i) ∩ (S.B j),{
      rw same, exact S.sp i hi.1 j hj.1,}, cases hj, cases hi, dsimp at *,
      ext1, simp only [mem_inter, mem_erase, ne.def, and.congr_left_iff, and_iff_right_iff_imp] at *,
      intros m n p, cases p,solve_by_elim,
  end,
  U:= (S.I.filter(λi, x∉(S.B i))).bUnion(λ i, (((S.A i).erase x) ∪ (S.B i ))),
  Ug:=rfl,  
  u:=card((S.I.filter(λi, x∉(S.B i))).bUnion(λ i, (((S.A i).erase x) ∪ (S.B i )))),
  ug:=rfl,
  spi:=begin
    intros i hi,
    rw [mem_filter] at *,
    apply disjoint_of_subset_left _ (S.spi i hi.1), apply erase_subset _,end,
}

--- the sets are in the universe...
lemma univ_ss {S : setpair} {i : ℕ} : i ∈ S.I → (S.A i ∪ S.B i)⊆ S.U:=
begin
  intro hi, intros x, rw [setpair.Ug,mem_bUnion],tauto,
end
-- applying er y gives a smaller universe if y was in the universe.
lemma er_univ_lt (S : setpair) {y : ℕ} : y ∈ S.U → (er S y).u < S.u :=
begin
  intro hy,
  have ss: (er S y).U ⊆ S.U,{
    simp [er,S.Ug], intros i hi hy, intros x hx, rw [mem_bUnion], use i ,
    split, exact hi, rw [mem_union] at *, cases hx with ha hb,
    left, apply mem_of_mem_erase ha,right, exact hb,},
  have ey: y∉ (er S y).U, {simp [er,S.Ug]},
  simp [setpair.ug],
  apply card_lt_card,
  apply  (ssubset_iff_of_subset ss).mpr _, 
  use [y, hy, ey], 
end

-- pairs are disjoint so sizes add.
lemma card_pair {S : setpair} {i : ℕ} : i  ∈ S.I → card((S.A i ∪ S.B i)) = card(S.A i) + card(S.B i):=λ hi, card_union_eq (S.spi i hi)
-- U is partitioned into each pair and their complement
lemma card_U {S :setpair} {i : ℕ} : i ∈ S.I → card(S.U\(S.A i ∪ S.B i)) + card(S.A i) + card(S.B i) = card(S.U):=
begin
  intros hi, rw [add_assoc, ← card_pair hi],
  apply card_sdiff_add_card_eq_card (univ_ss hi),
end

lemma card_Udiv (S :setpair) :∀i∈ S.I, ((card(S.A i) + card(S.B i)).choose (card(S.B i)):ℚ)⁻¹*(card S.U)=
((card(S.A i) + card(S.B i)).choose (card (S.B i)):ℚ)⁻¹*((card(S.U\(S.A i ∪ S.B i)) + card(S.A i) + card(S.B i))) :=
begin
  intros i hi, rw ← card_U hi, norm_cast,
end


--- want to work mainly with non-trivial setpairs so assume ever A i is non-empty
def triv_sp (S : setpair) : Prop := (∃i∈S.I, card(S.A i) =0) 
--- trivial sp has at most one pair.
lemma triv_imp_I1 {S :setpair} (h: triv_sp S) : card S.I ≤ 1:=
begin
  by_contra h', 
    obtain ⟨a,ha,b,hb,ne⟩:=one_lt_card.mp (by linarith: 1< S.I.card),
    obtain ⟨x,hx⟩:=(S.sp a ha b hb).mpr ne,
    obtain ⟨i,h⟩:=h,
    rw card_eq_zero at h,
    cases h with hi hie,
    rw mem_inter at hx,
    have ia: i=a, {
      apply sp' hi ha  _, rw hie, simp only [disjoint_empty_left],
    },
    have ib: i=b, {
      apply sp' hi hb  _, rw hie, simp only [disjoint_empty_left],
    },
    rw [←ia,←ib] at ne, tauto,
end


-- non-trivial means each A i is non-empty so has at least one element
lemma ntriv_sp {S : setpair} (ht: ¬triv_sp S): ∀i∈S.I, 1 ≤ card(S.A i):=
begin
  rw triv_sp at ht,push_neg at ht, intros i hi,  
  exact one_le_iff_ne_zero.mpr  (ht i hi),
end

-- making the casting of the densities slightly less painful
lemma binhelp {a b c d: ℕ } (h: (a+b)*c=d*a) (hc: 0 < c) (hd: 0 < d): (↑d:ℚ)⁻¹*(a+b)=(↑c:ℚ)⁻¹*a:=
begin
  have qh:((a:ℚ)+(b:ℚ))*(c:ℚ)=(d:ℚ)*(a:ℚ), norm_cast, exact h,
  have dnz: (d:ℚ)≠ 0,
  { simp only [ne.def, cast_eq_zero],  linarith,  },
  have cnz: (c:ℚ)≠ 0,
  { simp only [ne.def, cast_eq_zero],  linarith,  },
   rw ← div_eq_inv_mul,rw ← div_eq_inv_mul, 
   rw div_eq_iff dnz, rw mul_comm, rw mul_div,
    rw mul_comm,
    symmetry,
    rw  div_eq_iff cnz, symmetry, rw mul_comm (↑a), exact qh,
end

-- the key fact we need for binomials -- really should have done this in the nats.
lemma binom_frac (a b : ℕ) (h:0 < a) :((a+b).choose(b):ℚ)⁻¹*(a+b)=((a-1+b).choose(b):ℚ)⁻¹*a:=
begin
  have a1: a= (a -1).succ,{
    rw succ_eq_add_one, linarith,},
  have ab: a+b= (a-1+b).succ,{
    rw [succ_eq_add_one, add_assoc,add_comm b 1,← add_assoc,←succ_eq_add_one,← a1],},  
  have ch: (a-1+b).succ* (a-1+b).choose (a-1)= (a-1+b).succ.choose((a-1).succ)*((a-1).succ),
  apply succ_mul_choose_eq (a-1+b) (a-1),
  rw [←ab,← a1] at ch,
  have abn: (a-1+b)-(a-1)=b:=add_tsub_cancel_left (a-1) b, 
  have abs : a+b-a=b:=add_tsub_cancel_left a b,
  have aln: a-1 ≤ a-1+b:=(by linarith),
  have aln2: a≤ a+b:=(by linarith),
  have f1:  (a-1+b).choose((a-1+b)-(a-1))=(a-1+b).choose(a-1):=choose_symm aln,
  rw abn at f1,
  have f2:  (a+b).choose(a+b-a)=(a+b).choose(a):=choose_symm aln2,
  rw abs at f2,
  rw [←f1, ← f2] at ch,
 -- clear_except ch,
  rw [mul_comm],
  norm_cast,
  rw [mul_comm], simp [ch],
  have ap :(a-1+b).choose b > 0,{
    apply choose_pos (by linarith: b≤ a-1+b),
  },
  have bp:(a+b).choose b >0,{
    apply choose_pos (by linarith:b≤a+b),},
  apply binhelp ch ap bp, 
end

lemma den_rhs_1   {S : setpair} : ∑ i in S.I, ((card(S.A i) + card(S.B i)).choose (card (S.B i)):ℚ)⁻¹*card(S.U\(S.A i ∪ S.B i)) +
∑ i in S.I, ((card(S.A i) + card(S.B i)).choose (card (S.B i)):ℚ)⁻¹*(card(S.A i) + card(S.B i))
= den S * S.u :=
begin
  simp only [den, one_div], rw [setpair.ug],rw sum_mul, rw ← sum_add_distrib,
  apply sum_congr _ _, refl,
  intros i hi, rw ← mul_add, norm_cast, rw ← add_assoc, 
  convert card_Udiv S i hi, exact card_U hi, norm_cast, exact (card_U hi).symm,
end

lemma den_rhs_2   {S : setpair} (ht: ¬triv_sp S) : ∑ i in S.I, ((card(S.A i) + card(S.B i)).choose (card (S.B i)):ℚ)⁻¹*(card(S.A i) + card(S.B i)) =
∑ i in S.I, ((card(S.A i)-1 + card(S.B i)).choose (card (S.B i)):ℚ)⁻¹*(card(S.A i))
 :=
begin
  apply sum_congr _ _, refl, 
  intros i hi, rw binom_frac _ _ ((ntriv_sp ht) i hi),
end

lemma den_help_1 {S : setpair}  : ∀i, ∀y∈(S.U\((S.A i)∪(S.B i))), (S.A i).card +(S.B i).card = ((S.A i).erase y).card + (S.B i).card:=
begin
  intros i  y hy, simp only [add_left_inj], rw card_erase_eq_ite,split_ifs,
  simp only [*, mem_sdiff, mem_union, true_or, not_true, and_false] at *,
end

lemma den_help_2 {S : setpair}  : ∀i, ∀y∈(S.A i), (S.A i).card - 1 +(S.B i).card = ((S.A i).erase y).card + (S.B i).card:=
begin
  intros i  y hy, simp only [add_left_inj], rw card_erase_of_mem hy,
end

lemma den_rhs_3 {S : setpair}  : ∀ i∈S.I , ((card(S.A i) + card(S.B i)).choose (card (S.B i)):ℚ)⁻¹*(card(S.U\((S.A i)∪(S.B i)))) =
∑y in (S.U\((S.A i)∪(S.B i))), ((((S.A i).erase y).card + card(S.B i)).choose ((S.B i).card):ℚ)⁻¹:=
begin
  intros i hi, rw card_eq_sum_ones (S.U\((S.A i)∪(S.B i))),
  push_cast, rw zero_add, rw mul_sum, rw mul_one, 
  rw sum_congr _ _, refl,
  intros y hy,rw (den_help_1  i  y hy),
end


lemma den_rhs_4 {S : setpair}  : ∀ i∈S.I , ((card(S.A i) - 1 + card(S.B i)).choose (card (S.B i)):ℚ)⁻¹*(card(S.A i)) =
∑y in (S.A i), ((((S.A i).erase y).card + card(S.B i)).choose ((S.B i).card):ℚ)⁻¹:=
begin
  intros i hi, nth_rewrite 1  card_eq_sum_ones (S.A i),
  push_cast, rw zero_add, rw mul_sum, rw mul_one, 
  rw sum_congr _ _, refl,
  intros y hy,rw (den_help_2  i y hy),
end

lemma den_rhs_5 {S : setpair}  : ∑ i in S.I , ((card(S.A i) + card(S.B i)).choose (card (S.B i)):ℚ)⁻¹*(card(S.U\((S.A i)∪(S.B i)))) =
 ∑ i in S.I, (∑y in (S.U\((S.A i)∪(S.B i))), ((((S.A i).erase y).card + card(S.B i)).choose ((S.B i).card):ℚ)⁻¹):=
begin
  apply  sum_congr (rfl) (den_rhs_3),
end

lemma den_rhs_6 {S : setpair} : ∑ i in S.I, ((card(S.A i) - 1 + card(S.B i)).choose (card (S.B i)):ℚ)⁻¹*(card(S.A i)) =
∑ i in S.I, (∑y in (S.A i), ((((S.A i).erase y).card + card(S.B i)).choose ((S.B i).card):ℚ)⁻¹):=
begin
  apply  sum_congr (rfl) (den_rhs_4),
end


lemma disj_den {S : setpair}  : ∀i, disjoint (S.U\((S.A i)∪(S.B i))) (S.A i):=
begin
  intros i, 
  apply disjoint_of_subset_right (subset_union_left (S.A i) (S.B i)), 
  exact sdiff_disjoint,
end


lemma sp_sdiff (S : setpair) : ∀i∈S.I, (S.U\((S.A i)∪(S.B i)))∪ (S.A i) = (S.U\(S.B i)) :=
begin
  intros i hi,
  have he: (S.A i)∪ (S.B i)⊆ S.U:=univ_ss hi,
  have heA: (S.A i)⊆ S.U:=subset_trans (subset_union_left (S.A i) (S.B i)) he,
  have ab: disjoint (S.A i) (S.B i):=S.spi i hi,  
  rw sdiff_union_distrib, ext x,split, simp only [mem_union, mem_inter, mem_sdiff] at *,
  intro h, 
  rcases h, exact h.2, split, exact heA h, intro hb,
  exact  ab (mem_inter.mpr ⟨h,hb⟩),
  intros h, rw [mem_union,mem_inter,mem_sdiff],
  by_cases hA: x∈ (S.A i) ,
    right, exact hA, left,split, simp only [*, mem_sdiff, not_false_iff, and_self] at *, exact h,
end

lemma den_rhs_7 {S : setpair} : ∀i∈ S.I, (∑y in (S.U\((S.A i)∪(S.B i))), ((((S.A i).erase y).card + card(S.B i)).choose ((S.B i).card):ℚ)⁻¹)
+(∑y in (S.A i), ((((S.A i).erase y).card + card(S.B i)).choose ((S.B i).card):ℚ)⁻¹)=(∑y in (S.U\(S.B i)), ((((S.A i).erase y).card + card(S.B i)).choose ((S.B i).card):ℚ)⁻¹)
:=
begin
  intros i hi, rw [← sp_sdiff S i hi, sum_union (disj_den i )],
end

lemma den_rhs_8 {S : setpair}  : ∑ i in S.I, ((∑y in (S.U\((S.A i)∪(S.B i))), ((((S.A i).erase y).card + card(S.B i)).choose ((S.B i).card):ℚ)⁻¹)
+(∑y in (S.A i), ((((S.A i).erase y).card + card(S.B i)).choose ((S.B i).card):ℚ)⁻¹))=∑ i in S.I,(∑y in (S.U\(S.B i)), ((((S.A i).erase y).card + card(S.B i)).choose ((S.B i).card):ℚ)⁻¹)
:=
begin
   apply sum_congr (rfl) (den_rhs_7),
end



lemma doublecount {A B : finset ℕ} {f: ℕ → ℕ → ℚ}  {p: ℕ → ℕ → Prop} [decidable_rel p] :
 ∑ a in A, ∑ b in filter (λ i , p a i) B, f a b = ∑ b in B, ∑ a in filter (λ i, p i b) A, f a b:=
begin
  have inL: ∀a∈A,∑ b in filter (λ i, p a i) B, (f a b)= ∑ b in B, ite (p a b) (f a b) 0,{
      intros a ha, rw sum_filter,},
  have inL2: ∑a in A, ∑ b in filter (λ i, p a i) B, (f a b)= ∑ a in A, ∑ b in B, ite (p a b) (f a b) 0, {
      apply sum_congr, refl, exact inL,},
  have inR: ∀b∈B,∑ a in filter (λ i, p i b) A, (f a b)= ∑ a in A, ite (p a b) (f a b) 0,{
    intros b hb, rw sum_filter,},
  have inR2: ∑b in B, ∑ a in filter (λ i, p i b) A, (f a b)= ∑ b in B, ∑ a in A, ite (p a b) (f a b) 0, {
      apply sum_congr, refl, exact inR,},
  rw [inL2,inR2,sum_comm],
end

lemma doublecount' {A B : finset ℕ} {f g: ℕ → ℕ → ℚ} {a b : ℕ} {p: ℕ → ℕ → Prop} [decidable_rel p] : (∀a∈ A,∀b∈B , p a b → f a b = g a b)
 → ∑ a in A, ∑ b in filter (λ i , p a i) B, f a b = ∑ b in B, ∑ a in filter (λ i, p i b) A, g a b:=
begin
  intros h, rw doublecount, apply sum_congr, refl, intros b hb, apply sum_congr, refl,
  intro x, rw mem_filter, intro ha, exact h x ha.1 b hb ha.2,
end



lemma dc_4 {S : setpair} {f: ℕ → ℕ → ℚ} : ∑ i in S.I, ∑ y in S.U\(S.B i), f y i = ∑ i in S.I, ∑ y in filter (λ x, x∉(S.B i)) S.U, f y i:=
begin
  have H: ∀ i∈S.I, S.U\S.B i = filter (λ x, x∉ S.B i) S.U,{
    intros i hi, ext x,rw [mem_sdiff,mem_filter],},
  have H1: ∀ i∈S.I,∑ y in S.U\(S.B i), f y i =  ∑ y in filter (λ x, x∉(S.B i)) S.U, f y i,{
    intros i hi, apply sum_congr , exact H i hi, intros x hx,refl,},
    apply sum_congr, refl,exact H1,  
end

lemma den_double {S : setpair} (ht: ¬triv_sp S) : (∑  y in S.U, den (er S y))= den S * S.u  := 
begin
  rw ← den_rhs_1,  simp only [den, er, one_div],
  rw [den_rhs_2 ht, den_rhs_5 , den_rhs_6 , ←  sum_add_distrib],
  rw [den_rhs_8,dc_4,doublecount],
end

lemma trival_mem {S : setpair} (h: ∃i∈S.I, (S.A i) = ∅) : card S.I ≤ 1 :=
begin
  by_contra h', 
  obtain ⟨a,ha,b,hb,ne⟩:=one_lt_card.mp (by linarith: 1< S.I.card),
  obtain ⟨x,hx⟩:=(S.sp a ha b hb).mpr ne,
  obtain ⟨i, hi, inem⟩:=h,
  rw mem_inter at hx, 
  have ha' : disjoint (S.A i) (S.B a),
    rw inem, simp only [disjoint_empty_left],
  have hb' : disjoint (S.A i) (S.B b),
    rw inem, simp only [disjoint_empty_left],
  have ia: i=a:=sp'  hi ha ha', 
  have ib: i=b:=sp'  hi hb hb', 
  rw ia at ib, tauto, 
end

lemma trival_univ {S : setpair} (h: S.u = 0) : card S.I ≤ 1 :=
begin
  by_contra h', 
  obtain ⟨a,ha,b,hb,ne⟩:=one_lt_card.mp (by linarith: 1< S.I.card),
  obtain ⟨x,hx⟩:=(S.sp a ha b hb).mpr ne,
  have xinU: x∈ S.U,{
    simp only [mem_inter, setpair.Ug, mem_bUnion, mem_union, exists_prop, not_le, _root_.ne.def] at *,
    use [a,ha,hx.1], },
  rw [setpair.ug,card_eq_zero] at h, 
  have :S.U.nonempty:=⟨x,xinU⟩,   
    rw h at this, apply not_nonempty_empty this,
end


lemma den_triv {S : setpair} (h: triv_sp S) :den S≤ 1:=
begin
  have I1: card(S.I) ≤ 1:=triv_imp_I1 h,
  have Ic: card S.I ∈ Icc 0 1, {
  simp only [mem_Icc, zero_le, true_and,I1],},
  fin_cases Ic,
  {-- empty sum is zero
    have : den S =0,{
    rw card_eq_zero at Ic, rw [den, Ic],
    apply sum_empty,
    },linarith,
  },
  {--- only have I={a} so sum over singleton
    rw card_eq_one at Ic, rw [den],
    cases Ic with a ha, rw ha,
    rw sum_singleton, 
    set d:=((S.A a).card + (S.B a).card).choose ((S.B a).card),
    have nch: 0< d :=choose_pos (le_add_self),
    have d1: 1 ≤ d:= by linarith, 
    clear_except d1,
    rw one_div, apply inv_le_one _, rwa one_le_cast,
  },  
end


lemma emp_U_den {S : setpair} (h: S.u = 0): den S ≤ 1 :=
begin
  have Ic: card S.I ∈ Icc 0 1, {
  simp only [mem_Icc, zero_le, true_and, trival_univ h],},
  fin_cases Ic,
  {-- empty sum is zero
    have : den S =0,{
    rw card_eq_zero at Ic, rw [den, Ic],
    apply sum_empty,
    },linarith,
  },
  {--- only have I={a} so sum over singleton
    rw card_eq_one at Ic, rw [den],
    cases Ic with a ha, rw ha,
    rw sum_singleton, 
    set d:=((S.A a).card + (S.B a).card).choose ((S.B a).card),
    have nch: 0< d :=choose_pos (le_add_self),
    have d1: 1 ≤ d:= by linarith, 
    clear_except d1,
    rw one_div, apply inv_le_one _, rwa one_le_cast,
  },  
end

theorem bollobas_sp {S : setpair} {n : ℕ}: S.u=n →  den S ≤ 1 :=
begin
  revert S,
  --- should really do induction on S.wA so n= 0 → I.nonempty → (∃i∈S.I, (S.A i) = ∅) 
  induction n using nat.strong_induction_on with n hn,
  intros S hs,
  cases nat.eq_zero_or_pos n with Uem,
  {rw ← hs at Uem, exact emp_U_den Uem,},
   by_cases ht: triv_sp S,
   {--- do case where there is an empty set in A or no sets at all!
    exact den_triv ht, },
  { rw ← hs at h,
    apply (mul_le_iff_le_one_left (cast_pos.mpr h)).mp, 
    have e: (∑  y in S.U, den (er S y)) = den S * S.u,{
      exact den_double ht,},
    rw ← e,
    have dc: ∀y∈ S.U, (er S y).u< S.u,{
      intros y hy, exact er_univ_lt S hy,},
    have dd: ∀y∈ S.U, den(er S y)≤ (1:ℚ),{
      intros y hy, rw hs at dc,
      apply  hn ((er S y).u) (dc y hy),refl,},
  { rw setpair.ug,
    rw card_eq_sum_ones, 
    convert sum_le_sum dd, norm_cast,},
    exact rat.nontrivial, },
end





theorem bollobas_sp' {S : setpair} : den S ≤ 1 :=
begin
  set n:ℕ:=S.u with h, exact bollobas_sp h,
end
end bbsetpair2
end finset

