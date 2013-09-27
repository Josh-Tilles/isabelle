(*  Title:      HOL/Library/FSet.thy
    Author:     Ondrej Kuncar, TU Muenchen
    Author:     Cezary Kaliszyk and Christian Urban
*)

header {* Type of finite sets defined as a subtype of sets *}

theory FSet
imports Main Conditionally_Complete_Lattices
begin

subsection {* Definition of the type *}

typedef 'a fset = "{A :: 'a set. finite A}"  morphisms fset Abs_fset
by auto

setup_lifting type_definition_fset

subsection {* Basic operations and type class instantiations *}

(* FIXME transfer and right_total vs. bi_total *)
instantiation fset :: (finite) finite
begin
instance by default (transfer, simp)
end

instantiation fset :: (type) "{bounded_lattice_bot, distrib_lattice, minus}"
begin

interpretation lifting_syntax .

lift_definition bot_fset :: "'a fset" is "{}" parametric empty_transfer by simp 

lift_definition less_eq_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" is subset_eq parametric subset_transfer 
  by simp

definition less_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" where "xs < ys \<equiv> xs \<le> ys \<and> xs \<noteq> (ys::'a fset)"

lemma less_fset_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" 
  shows "((pcr_fset A) ===> (pcr_fset A) ===> op =) op \<subset> op <"
  unfolding less_fset_def[abs_def] psubset_eq[abs_def] by transfer_prover
  

lift_definition sup_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is union parametric union_transfer
  by simp

lift_definition inf_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is inter parametric inter_transfer
  by simp

lift_definition minus_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is minus parametric Diff_transfer
  by simp

instance
by default (transfer, auto)+

end

abbreviation fempty :: "'a fset" ("{||}") where "{||} \<equiv> bot"
abbreviation fsubset_eq :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "|\<subseteq>|" 50) where "xs |\<subseteq>| ys \<equiv> xs \<le> ys"
abbreviation fsubset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "|\<subset>|" 50) where "xs |\<subset>| ys \<equiv> xs < ys"
abbreviation funion :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" (infixl "|\<union>|" 65) where "xs |\<union>| ys \<equiv> sup xs ys"
abbreviation finter :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" (infixl "|\<inter>|" 65) where "xs |\<inter>| ys \<equiv> inf xs ys"
abbreviation fminus :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" (infixl "|-|" 65) where "xs |-| ys \<equiv> minus xs ys"

instantiation fset :: (type) conditionally_complete_lattice
begin

interpretation lifting_syntax .

lemma right_total_Inf_fset_transfer:
  assumes [transfer_rule]: "bi_unique A" and [transfer_rule]: "right_total A"
  shows "(set_rel (set_rel A) ===> set_rel A) 
    (\<lambda>S. if finite (Inter S \<inter> Collect (Domainp A)) then Inter S \<inter> Collect (Domainp A) else {}) 
      (\<lambda>S. if finite (Inf S) then Inf S else {})"
    by transfer_prover

lemma Inf_fset_transfer:
  assumes [transfer_rule]: "bi_unique A" and [transfer_rule]: "bi_total A"
  shows "(set_rel (set_rel A) ===> set_rel A) (\<lambda>A. if finite (Inf A) then Inf A else {}) 
    (\<lambda>A. if finite (Inf A) then Inf A else {})"
  by transfer_prover

lift_definition Inf_fset :: "'a fset set \<Rightarrow> 'a fset" is "\<lambda>A. if finite (Inf A) then Inf A else {}" 
parametric right_total_Inf_fset_transfer Inf_fset_transfer by simp

lemma Sup_fset_transfer:
  assumes [transfer_rule]: "bi_unique A"
  shows "(set_rel (set_rel A) ===> set_rel A) (\<lambda>A. if finite (Sup A) then Sup A else {})
  (\<lambda>A. if finite (Sup A) then Sup A else {})" by transfer_prover

lift_definition Sup_fset :: "'a fset set \<Rightarrow> 'a fset" is "\<lambda>A. if finite (Sup A) then Sup A else {}"
parametric Sup_fset_transfer by simp

lemma finite_Sup: "\<exists>z. finite z \<and> (\<forall>a. a \<in> X \<longrightarrow> a \<le> z) \<Longrightarrow> finite (Sup X)"
by (auto intro: finite_subset)

instance
proof 
  fix x z :: "'a fset"
  fix X :: "'a fset set"
  {
    assume "x \<in> X" "(\<And>a. a \<in> X \<Longrightarrow> z |\<subseteq>| a)" 
    then show "Inf X |\<subseteq>| x"  by transfer auto
  next
    assume "X \<noteq> {}" "(\<And>x. x \<in> X \<Longrightarrow> z |\<subseteq>| x)"
    then show "z |\<subseteq>| Inf X" by transfer (clarsimp, blast)
  next
    assume "x \<in> X" "(\<And>a. a \<in> X \<Longrightarrow> a |\<subseteq>| z)"
    then show "x |\<subseteq>| Sup X" by transfer (auto intro!: finite_Sup)
  next
    assume "X \<noteq> {}" "(\<And>x. x \<in> X \<Longrightarrow> x |\<subseteq>| z)"
    then show "Sup X |\<subseteq>| z" by transfer (clarsimp, blast)
  }
qed
end

instantiation fset :: (finite) complete_lattice 
begin

lift_definition top_fset :: "'a fset" is UNIV parametric right_total_UNIV_transfer UNIV_transfer by simp

instance by default (transfer, auto)+
end

instantiation fset :: (finite) complete_boolean_algebra
begin

lift_definition uminus_fset :: "'a fset \<Rightarrow> 'a fset" is uminus 
  parametric right_total_Compl_transfer Compl_transfer by simp

instance by (default, simp_all only: INF_def SUP_def) (transfer, auto)+

end

abbreviation fUNIV :: "'a::finite fset" where "fUNIV \<equiv> top"
abbreviation fuminus :: "'a::finite fset \<Rightarrow> 'a fset" ("|-| _" [81] 80) where "|-| x \<equiv> uminus x"

subsection {* Other operations *}

lift_definition finsert :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is insert parametric Lifting_Set.insert_transfer
  by simp

syntax
  "_insert_fset"     :: "args => 'a fset"  ("{|(_)|}")

translations
  "{|x, xs|}" == "CONST finsert x {|xs|}"
  "{|x|}"     == "CONST finsert x {||}"

lift_definition fmember :: "'a \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "|\<in>|" 50) is Set.member 
  parametric member_transfer by simp

abbreviation notin_fset :: "'a \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "|\<notin>|" 50) where "x |\<notin>| S \<equiv> \<not> (x |\<in>| S)"

context
begin
interpretation lifting_syntax .

lift_definition ffilter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is Set.filter 
  parametric Lifting_Set.filter_transfer unfolding Set.filter_def by simp

lemma compose_rel_to_Domainp:
  assumes "left_unique R"
  assumes "(R ===> op=) P P'"
  shows "(R OO Lifting.invariant P' OO R\<inverse>\<inverse>) x y \<longleftrightarrow> Domainp R x \<and> P x \<and> x = y"
using assms unfolding OO_def conversep_iff Domainp_iff left_unique_def fun_rel_def invariant_def
by blast

lift_definition fPow :: "'a fset \<Rightarrow> 'a fset fset" is Pow parametric Pow_transfer 
by (subst compose_rel_to_Domainp [OF _ finite_transfer]) (auto intro: transfer_raw finite_subset 
  simp add: fset.pcr_cr_eq[symmetric] Domainp_set fset.domain_eq)

lift_definition fcard :: "'a fset \<Rightarrow> nat" is card parametric card_transfer by simp

lift_definition fimage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b fset" (infixr "|`|" 90) is image 
  parametric image_transfer by simp

lift_definition fthe_elem :: "'a fset \<Rightarrow> 'a" is the_elem ..

(* FIXME why is not invariant here unfolded ? *)
lift_definition fbind :: "'a fset \<Rightarrow> ('a \<Rightarrow> 'b fset) \<Rightarrow> 'b fset" is Set.bind parametric bind_transfer
unfolding invariant_def Set.bind_def by clarsimp metis

lift_definition ffUnion :: "'a fset fset \<Rightarrow> 'a fset" is Union parametric Union_transfer
by (subst(asm) compose_rel_to_Domainp [OF _ finite_transfer])
  (auto intro: transfer_raw simp add: fset.pcr_cr_eq[symmetric] Domainp_set fset.domain_eq invariant_def)

lift_definition fBall :: "'a fset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" is Ball parametric Ball_transfer ..
lift_definition fBex :: "'a fset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" is Bex parametric Bex_transfer ..

lift_definition ffold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a fset \<Rightarrow> 'b" is Finite_Set.fold ..

subsection {* Transferred lemmas from Set.thy *}

lemmas fset_eqI = set_eqI[Transfer.transferred]
lemmas fset_eq_iff[no_atp] = set_eq_iff[Transfer.transferred]
lemmas fBallI[intro!] = ballI[Transfer.transferred]
lemmas fbspec[dest?] = bspec[Transfer.transferred]
lemmas fBallE[elim] = ballE[Transfer.transferred]
lemmas fBexI[intro] = bexI[Transfer.transferred]
lemmas rev_fBexI[intro?] = rev_bexI[Transfer.transferred]
lemmas fBexCI = bexCI[Transfer.transferred]
lemmas fBexE[elim!] = bexE[Transfer.transferred]
lemmas fBall_triv[simp] = ball_triv[Transfer.transferred]
lemmas fBex_triv[simp] = bex_triv[Transfer.transferred]
lemmas fBex_triv_one_point1[simp] = bex_triv_one_point1[Transfer.transferred]
lemmas fBex_triv_one_point2[simp] = bex_triv_one_point2[Transfer.transferred]
lemmas fBex_one_point1[simp] = bex_one_point1[Transfer.transferred]
lemmas fBex_one_point2[simp] = bex_one_point2[Transfer.transferred]
lemmas fBall_one_point1[simp] = ball_one_point1[Transfer.transferred]
lemmas fBall_one_point2[simp] = ball_one_point2[Transfer.transferred]
lemmas fBall_conj_distrib = ball_conj_distrib[Transfer.transferred]
lemmas fBex_disj_distrib = bex_disj_distrib[Transfer.transferred]
lemmas fBall_cong = ball_cong[Transfer.transferred]
lemmas fBex_cong = bex_cong[Transfer.transferred]
lemmas fsubsetI[intro!] = subsetI[Transfer.transferred]
lemmas fsubsetD[elim, intro?] = subsetD[Transfer.transferred]
lemmas rev_fsubsetD[no_atp,intro?] = rev_subsetD[Transfer.transferred]
lemmas fsubsetCE[no_atp,elim] = subsetCE[Transfer.transferred]
lemmas fsubset_eq[no_atp] = subset_eq[Transfer.transferred]
lemmas contra_fsubsetD[no_atp] = contra_subsetD[Transfer.transferred]
lemmas fsubset_refl = subset_refl[Transfer.transferred]
lemmas fsubset_trans = subset_trans[Transfer.transferred]
lemmas fset_rev_mp = set_rev_mp[Transfer.transferred]
lemmas fset_mp = set_mp[Transfer.transferred]
lemmas fsubset_not_fsubset_eq[code] = subset_not_subset_eq[Transfer.transferred]
lemmas eq_fmem_trans = eq_mem_trans[Transfer.transferred]
lemmas fsubset_antisym[intro!] = subset_antisym[Transfer.transferred]
lemmas fequalityD1 = equalityD1[Transfer.transferred]
lemmas fequalityD2 = equalityD2[Transfer.transferred]
lemmas fequalityE = equalityE[Transfer.transferred]
lemmas fequalityCE[elim] = equalityCE[Transfer.transferred]
lemmas eqfset_imp_iff = eqset_imp_iff[Transfer.transferred]
lemmas eqfelem_imp_iff = eqelem_imp_iff[Transfer.transferred]
lemmas fempty_iff[simp] = empty_iff[Transfer.transferred]
lemmas fempty_fsubsetI[iff] = empty_subsetI[Transfer.transferred]
lemmas equalsffemptyI = equals0I[Transfer.transferred]
lemmas equalsffemptyD = equals0D[Transfer.transferred]
lemmas fBall_fempty[simp] = ball_empty[Transfer.transferred]
lemmas fBex_fempty[simp] = bex_empty[Transfer.transferred]
lemmas fPow_iff[iff] = Pow_iff[Transfer.transferred]
lemmas fPowI = PowI[Transfer.transferred]
lemmas fPowD = PowD[Transfer.transferred]
lemmas fPow_bottom = Pow_bottom[Transfer.transferred]
lemmas fPow_top = Pow_top[Transfer.transferred]
lemmas fPow_not_fempty = Pow_not_empty[Transfer.transferred]
lemmas finter_iff[simp] = Int_iff[Transfer.transferred]
lemmas finterI[intro!] = IntI[Transfer.transferred]
lemmas finterD1 = IntD1[Transfer.transferred]
lemmas finterD2 = IntD2[Transfer.transferred]
lemmas finterE[elim!] = IntE[Transfer.transferred]
lemmas funion_iff[simp] = Un_iff[Transfer.transferred]
lemmas funionI1[elim?] = UnI1[Transfer.transferred]
lemmas funionI2[elim?] = UnI2[Transfer.transferred]
lemmas funionCI[intro!] = UnCI[Transfer.transferred]
lemmas funionE[elim!] = UnE[Transfer.transferred]
lemmas fminus_iff[simp] = Diff_iff[Transfer.transferred]
lemmas fminusI[intro!] = DiffI[Transfer.transferred]
lemmas fminusD1 = DiffD1[Transfer.transferred]
lemmas fminusD2 = DiffD2[Transfer.transferred]
lemmas fminusE[elim!] = DiffE[Transfer.transferred]
lemmas finsert_iff[simp] = insert_iff[Transfer.transferred]
lemmas finsertI1 = insertI1[Transfer.transferred]
lemmas finsertI2 = insertI2[Transfer.transferred]
lemmas finsertE[elim!] = insertE[Transfer.transferred]
lemmas finsertCI[intro!] = insertCI[Transfer.transferred]
lemmas fsubset_finsert_iff = subset_insert_iff[Transfer.transferred]
lemmas finsert_ident = insert_ident[Transfer.transferred]
lemmas fsingletonI[intro!,no_atp] = singletonI[Transfer.transferred]
lemmas fsingletonD[dest!,no_atp] = singletonD[Transfer.transferred]
lemmas fsingleton_iff = singleton_iff[Transfer.transferred]
lemmas fsingleton_inject[dest!] = singleton_inject[Transfer.transferred]
lemmas fsingleton_finsert_inj_eq[iff,no_atp] = singleton_insert_inj_eq[Transfer.transferred]
lemmas fsingleton_finsert_inj_eq'[iff,no_atp] = singleton_insert_inj_eq'[Transfer.transferred]
lemmas fsubset_fsingletonD = subset_singletonD[Transfer.transferred]
lemmas fminus_single_finsert = diff_single_insert[Transfer.transferred]
lemmas fdoubleton_eq_iff = doubleton_eq_iff[Transfer.transferred]
lemmas funion_fsingleton_iff = Un_singleton_iff[Transfer.transferred]
lemmas fsingleton_funion_iff = singleton_Un_iff[Transfer.transferred]
lemmas fimage_eqI[simp, intro] = image_eqI[Transfer.transferred]
lemmas fimageI = imageI[Transfer.transferred]
lemmas rev_fimage_eqI = rev_image_eqI[Transfer.transferred]
lemmas fimageE[elim!] = imageE[Transfer.transferred]
lemmas Compr_fimage_eq = Compr_image_eq[Transfer.transferred]
lemmas fimage_funion = image_Un[Transfer.transferred]
lemmas fimage_iff = image_iff[Transfer.transferred]
lemmas fimage_fsubset_iff[no_atp] = image_subset_iff[Transfer.transferred]
lemmas fimage_fsubsetI = image_subsetI[Transfer.transferred]
lemmas fimage_ident[simp] = image_ident[Transfer.transferred]
lemmas split_if_fmem1 = split_if_mem1[Transfer.transferred]
lemmas split_if_fmem2 = split_if_mem2[Transfer.transferred]
lemmas pfsubsetI[intro!,no_atp] = psubsetI[Transfer.transferred]
lemmas pfsubsetE[elim!,no_atp] = psubsetE[Transfer.transferred]
lemmas pfsubset_finsert_iff = psubset_insert_iff[Transfer.transferred]
lemmas pfsubset_eq = psubset_eq[Transfer.transferred]
lemmas pfsubset_imp_fsubset = psubset_imp_subset[Transfer.transferred]
lemmas pfsubset_trans = psubset_trans[Transfer.transferred]
lemmas pfsubsetD = psubsetD[Transfer.transferred]
lemmas pfsubset_fsubset_trans = psubset_subset_trans[Transfer.transferred]
lemmas fsubset_pfsubset_trans = subset_psubset_trans[Transfer.transferred]
lemmas pfsubset_imp_ex_fmem = psubset_imp_ex_mem[Transfer.transferred]
lemmas fimage_fPow_mono = image_Pow_mono[Transfer.transferred]
lemmas fimage_fPow_surj = image_Pow_surj[Transfer.transferred]
lemmas fsubset_finsertI = subset_insertI[Transfer.transferred]
lemmas fsubset_finsertI2 = subset_insertI2[Transfer.transferred]
lemmas fsubset_finsert = subset_insert[Transfer.transferred]
lemmas funion_upper1 = Un_upper1[Transfer.transferred]
lemmas funion_upper2 = Un_upper2[Transfer.transferred]
lemmas funion_least = Un_least[Transfer.transferred]
lemmas finter_lower1 = Int_lower1[Transfer.transferred]
lemmas finter_lower2 = Int_lower2[Transfer.transferred]
lemmas finter_greatest = Int_greatest[Transfer.transferred]
lemmas fminus_fsubset = Diff_subset[Transfer.transferred]
lemmas fminus_fsubset_conv = Diff_subset_conv[Transfer.transferred]
lemmas fsubset_fempty[simp] = subset_empty[Transfer.transferred]
lemmas not_pfsubset_fempty[iff] = not_psubset_empty[Transfer.transferred]
lemmas finsert_is_funion = insert_is_Un[Transfer.transferred]
lemmas finsert_not_fempty[simp] = insert_not_empty[Transfer.transferred]
lemmas fempty_not_finsert = empty_not_insert[Transfer.transferred]
lemmas finsert_absorb = insert_absorb[Transfer.transferred]
lemmas finsert_absorb2[simp] = insert_absorb2[Transfer.transferred]
lemmas finsert_commute = insert_commute[Transfer.transferred]
lemmas finsert_fsubset[simp] = insert_subset[Transfer.transferred]
lemmas finsert_inter_finsert[simp] = insert_inter_insert[Transfer.transferred]
lemmas finsert_disjoint[simp,no_atp] = insert_disjoint[Transfer.transferred]
lemmas disjoint_finsert[simp,no_atp] = disjoint_insert[Transfer.transferred]
lemmas fimage_fempty[simp] = image_empty[Transfer.transferred]
lemmas fimage_finsert[simp] = image_insert[Transfer.transferred]
lemmas fimage_constant = image_constant[Transfer.transferred]
lemmas fimage_constant_conv = image_constant_conv[Transfer.transferred]
lemmas fimage_fimage = image_image[Transfer.transferred]
lemmas finsert_fimage[simp] = insert_image[Transfer.transferred]
lemmas fimage_is_fempty[iff] = image_is_empty[Transfer.transferred]
lemmas fempty_is_fimage[iff] = empty_is_image[Transfer.transferred]
lemmas fimage_cong = image_cong[Transfer.transferred]
lemmas fimage_finter_fsubset = image_Int_subset[Transfer.transferred]
lemmas fimage_fminus_fsubset = image_diff_subset[Transfer.transferred]
lemmas finter_absorb = Int_absorb[Transfer.transferred]
lemmas finter_left_absorb = Int_left_absorb[Transfer.transferred]
lemmas finter_commute = Int_commute[Transfer.transferred]
lemmas finter_left_commute = Int_left_commute[Transfer.transferred]
lemmas finter_assoc = Int_assoc[Transfer.transferred]
lemmas finter_ac = Int_ac[Transfer.transferred]
lemmas finter_absorb1 = Int_absorb1[Transfer.transferred]
lemmas finter_absorb2 = Int_absorb2[Transfer.transferred]
lemmas finter_fempty_left = Int_empty_left[Transfer.transferred]
lemmas finter_fempty_right = Int_empty_right[Transfer.transferred]
lemmas disjoint_iff_fnot_equal = disjoint_iff_not_equal[Transfer.transferred]
lemmas finter_funion_distrib = Int_Un_distrib[Transfer.transferred]
lemmas finter_funion_distrib2 = Int_Un_distrib2[Transfer.transferred]
lemmas finter_fsubset_iff[no_atp, simp] = Int_subset_iff[Transfer.transferred]
lemmas funion_absorb = Un_absorb[Transfer.transferred]
lemmas funion_left_absorb = Un_left_absorb[Transfer.transferred]
lemmas funion_commute = Un_commute[Transfer.transferred]
lemmas funion_left_commute = Un_left_commute[Transfer.transferred]
lemmas funion_assoc = Un_assoc[Transfer.transferred]
lemmas funion_ac = Un_ac[Transfer.transferred]
lemmas funion_absorb1 = Un_absorb1[Transfer.transferred]
lemmas funion_absorb2 = Un_absorb2[Transfer.transferred]
lemmas funion_fempty_left = Un_empty_left[Transfer.transferred]
lemmas funion_fempty_right = Un_empty_right[Transfer.transferred]
lemmas funion_finsert_left[simp] = Un_insert_left[Transfer.transferred]
lemmas funion_finsert_right[simp] = Un_insert_right[Transfer.transferred]
lemmas finter_finsert_left = Int_insert_left[Transfer.transferred]
lemmas finter_finsert_left_ifffempty[simp] = Int_insert_left_if0[Transfer.transferred]
lemmas finter_finsert_left_if1[simp] = Int_insert_left_if1[Transfer.transferred]
lemmas finter_finsert_right = Int_insert_right[Transfer.transferred]
lemmas finter_finsert_right_ifffempty[simp] = Int_insert_right_if0[Transfer.transferred]
lemmas finter_finsert_right_if1[simp] = Int_insert_right_if1[Transfer.transferred]
lemmas funion_finter_distrib = Un_Int_distrib[Transfer.transferred]
lemmas funion_finter_distrib2 = Un_Int_distrib2[Transfer.transferred]
lemmas funion_finter_crazy = Un_Int_crazy[Transfer.transferred]
lemmas fsubset_funion_eq = subset_Un_eq[Transfer.transferred]
lemmas funion_fempty[iff] = Un_empty[Transfer.transferred]
lemmas funion_fsubset_iff[no_atp, simp] = Un_subset_iff[Transfer.transferred]
lemmas funion_fminus_finter = Un_Diff_Int[Transfer.transferred]
lemmas fminus_finter2 = Diff_Int2[Transfer.transferred]
lemmas funion_finter_assoc_eq = Un_Int_assoc_eq[Transfer.transferred]
lemmas fBall_funion = ball_Un[Transfer.transferred]
lemmas fBex_funion = bex_Un[Transfer.transferred]
lemmas fminus_eq_fempty_iff[simp,no_atp] = Diff_eq_empty_iff[Transfer.transferred]
lemmas fminus_cancel[simp] = Diff_cancel[Transfer.transferred]
lemmas fminus_idemp[simp] = Diff_idemp[Transfer.transferred]
lemmas fminus_triv = Diff_triv[Transfer.transferred]
lemmas fempty_fminus[simp] = empty_Diff[Transfer.transferred]
lemmas fminus_fempty[simp] = Diff_empty[Transfer.transferred]
lemmas fminus_finsertffempty[simp,no_atp] = Diff_insert0[Transfer.transferred]
lemmas fminus_finsert = Diff_insert[Transfer.transferred]
lemmas fminus_finsert2 = Diff_insert2[Transfer.transferred]
lemmas finsert_fminus_if = insert_Diff_if[Transfer.transferred]
lemmas finsert_fminus1[simp] = insert_Diff1[Transfer.transferred]
lemmas finsert_fminus_single[simp] = insert_Diff_single[Transfer.transferred]
lemmas finsert_fminus = insert_Diff[Transfer.transferred]
lemmas fminus_finsert_absorb = Diff_insert_absorb[Transfer.transferred]
lemmas fminus_disjoint[simp] = Diff_disjoint[Transfer.transferred]
lemmas fminus_partition = Diff_partition[Transfer.transferred]
lemmas double_fminus = double_diff[Transfer.transferred]
lemmas funion_fminus_cancel[simp] = Un_Diff_cancel[Transfer.transferred]
lemmas funion_fminus_cancel2[simp] = Un_Diff_cancel2[Transfer.transferred]
lemmas fminus_funion = Diff_Un[Transfer.transferred]
lemmas fminus_finter = Diff_Int[Transfer.transferred]
lemmas funion_fminus = Un_Diff[Transfer.transferred]
lemmas finter_fminus = Int_Diff[Transfer.transferred]
lemmas fminus_finter_distrib = Diff_Int_distrib[Transfer.transferred]
lemmas fminus_finter_distrib2 = Diff_Int_distrib2[Transfer.transferred]
lemmas fUNIV_bool[no_atp] = UNIV_bool[Transfer.transferred]
lemmas fPow_fempty[simp] = Pow_empty[Transfer.transferred]
lemmas fPow_finsert = Pow_insert[Transfer.transferred]
lemmas funion_fPow_fsubset = Un_Pow_subset[Transfer.transferred]
lemmas fPow_finter_eq[simp] = Pow_Int_eq[Transfer.transferred]
lemmas fset_eq_fsubset = set_eq_subset[Transfer.transferred]
lemmas fsubset_iff[no_atp] = subset_iff[Transfer.transferred]
lemmas fsubset_iff_pfsubset_eq = subset_iff_psubset_eq[Transfer.transferred]
lemmas all_not_fin_conv[simp] = all_not_in_conv[Transfer.transferred]
lemmas ex_fin_conv = ex_in_conv[Transfer.transferred]
lemmas fimage_mono = image_mono[Transfer.transferred]
lemmas fPow_mono = Pow_mono[Transfer.transferred]
lemmas finsert_mono = insert_mono[Transfer.transferred]
lemmas funion_mono = Un_mono[Transfer.transferred]
lemmas finter_mono = Int_mono[Transfer.transferred]
lemmas fminus_mono = Diff_mono[Transfer.transferred]
lemmas fin_mono = in_mono[Transfer.transferred]
lemmas fthe_felem_eq[simp] = the_elem_eq[Transfer.transferred]
lemmas fLeast_mono = Least_mono[Transfer.transferred]
lemmas fbind_fbind = bind_bind[Transfer.transferred]
lemmas fempty_fbind[simp] = empty_bind[Transfer.transferred]
lemmas nonfempty_fbind_const = nonempty_bind_const[Transfer.transferred]
lemmas fbind_const = bind_const[Transfer.transferred]
lemmas ffmember_filter[simp] = member_filter[Transfer.transferred]
lemmas fequalityI = equalityI[Transfer.transferred]

subsection {* Additional lemmas*}

subsubsection {* fsingleton *}

lemmas fsingletonE = fsingletonD [elim_format]

subsubsection {* femepty *}

lemma fempty_ffilter[simp]: "ffilter (\<lambda>_. False) A = {||}"
by transfer auto

(* FIXME, transferred doesn't work here *)
lemma femptyE [elim!]: "a |\<in>| {||} \<Longrightarrow> P"
  by simp

subsubsection {* fset *}

lemmas fset_simps[simp] = bot_fset.rep_eq finsert.rep_eq

lemma finite_fset [simp]: 
  shows "finite (fset S)"
  by transfer simp

lemmas fset_cong = fset_inject

lemma filter_fset [simp]:
  shows "fset (ffilter P xs) = Collect P \<inter> fset xs"
  by transfer auto

lemma notin_fset: "x |\<notin>| S \<longleftrightarrow> x \<notin> fset S" by (simp add: fmember.rep_eq)

lemmas inter_fset[simp] = inf_fset.rep_eq

lemmas union_fset[simp] = sup_fset.rep_eq

lemmas minus_fset[simp] = minus_fset.rep_eq

subsubsection {* filter_fset *}

lemma subset_ffilter: 
  "ffilter P A |\<subseteq>| ffilter Q A = (\<forall> x. x |\<in>| A \<longrightarrow> P x \<longrightarrow> Q x)"
  by transfer auto

lemma eq_ffilter: 
  "(ffilter P A = ffilter Q A) = (\<forall>x. x |\<in>| A \<longrightarrow> P x = Q x)"
  by transfer auto

lemma pfsubset_ffilter:
  "(\<And>x. x |\<in>| A \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> (x |\<in>| A & \<not> P x & Q x) \<Longrightarrow> 
    ffilter P A |\<subset>| ffilter Q A"
  unfolding less_fset_def by (auto simp add: subset_ffilter eq_ffilter)

subsubsection {* finsert *}

(* FIXME, transferred doesn't work here *)
lemma set_finsert:
  assumes "x |\<in>| A"
  obtains B where "A = finsert x B" and "x |\<notin>| B"
using assms by transfer (metis Set.set_insert finite_insert)

lemma mk_disjoint_finsert: "a |\<in>| A \<Longrightarrow> \<exists>B. A = finsert a B \<and> a |\<notin>| B"
  by (rule_tac x = "A |-| {|a|}" in exI, blast)

subsubsection {* fimage *}

lemma subset_fimage_iff: "(B |\<subseteq>| f|`|A) = (\<exists> AA. AA |\<subseteq>| A \<and> B = f|`|AA)"
by transfer (metis mem_Collect_eq rev_finite_subset subset_image_iff)

subsubsection {* bounded quantification *}

lemma bex_simps [simp, no_atp]:
  "\<And>A P Q. fBex A (\<lambda>x. P x \<and> Q) = (fBex A P \<and> Q)" 
  "\<And>A P Q. fBex A (\<lambda>x. P \<and> Q x) = (P \<and> fBex A Q)"
  "\<And>P. fBex {||} P = False" 
  "\<And>a B P. fBex (finsert a B) P = (P a \<or> fBex B P)"
  "\<And>A P f. fBex (f |`| A) P = fBex A (\<lambda>x. P (f x))"
  "\<And>A P. (\<not> fBex A P) = fBall A (\<lambda>x. \<not> P x)"
by auto

lemma ball_simps [simp, no_atp]:
  "\<And>A P Q. fBall A (\<lambda>x. P x \<or> Q) = (fBall A P \<or> Q)"
  "\<And>A P Q. fBall A (\<lambda>x. P \<or> Q x) = (P \<or> fBall A Q)"
  "\<And>A P Q. fBall A (\<lambda>x. P \<longrightarrow> Q x) = (P \<longrightarrow> fBall A Q)"
  "\<And>A P Q. fBall A (\<lambda>x. P x \<longrightarrow> Q) = (fBex A P \<longrightarrow> Q)"
  "\<And>P. fBall {||} P = True"
  "\<And>a B P. fBall (finsert a B) P = (P a \<and> fBall B P)"
  "\<And>A P f. fBall (f |`| A) P = fBall A (\<lambda>x. P (f x))"
  "\<And>A P. (\<not> fBall A P) = fBex A (\<lambda>x. \<not> P x)"
by auto

lemma atomize_fBall:
    "(\<And>x. x |\<in>| A ==> P x) == Trueprop (fBall A (\<lambda>x. P x))"
apply (simp only: atomize_all atomize_imp)
apply (rule equal_intr_rule)
by (transfer, simp)+

end

subsubsection {* fcard *}

(* FIXME: improve transferred to handle bounded meta quantification *)

lemma fcard_fempty:
  "fcard {||} = 0"
  by transfer (rule card_empty)

lemma fcard_finsert_disjoint:
  "x |\<notin>| A \<Longrightarrow> fcard (finsert x A) = Suc (fcard A)"
  by transfer (rule card_insert_disjoint)

lemma fcard_finsert_if:
  "fcard (finsert x A) = (if x |\<in>| A then fcard A else Suc (fcard A))"
  by transfer (rule card_insert_if)

lemma card_0_eq [simp, no_atp]:
  "fcard A = 0 \<longleftrightarrow> A = {||}"
  by transfer (rule card_0_eq)

lemma fcard_Suc_fminus1:
  "x |\<in>| A \<Longrightarrow> Suc (fcard (A |-| {|x|})) = fcard A"
  by transfer (rule card_Suc_Diff1)

lemma fcard_fminus_fsingleton:
  "x |\<in>| A \<Longrightarrow> fcard (A |-| {|x|}) = fcard A - 1"
  by transfer (rule card_Diff_singleton)

lemma fcard_fminus_fsingleton_if:
  "fcard (A |-| {|x|}) = (if x |\<in>| A then fcard A - 1 else fcard A)"
  by transfer (rule card_Diff_singleton_if)

lemma fcard_fminus_finsert[simp]:
  assumes "a |\<in>| A" and "a |\<notin>| B"
  shows "fcard (A |-| finsert a B) = fcard (A |-| B) - 1"
using assms by transfer (rule card_Diff_insert)

lemma fcard_finsert: "fcard (finsert x A) = Suc (fcard (A |-| {|x|}))"
by transfer (rule card_insert)

lemma fcard_finsert_le: "fcard A \<le> fcard (finsert x A)"
by transfer (rule card_insert_le)

lemma fcard_mono:
  "A |\<subseteq>| B \<Longrightarrow> fcard A \<le> fcard B"
by transfer (rule card_mono)

lemma fcard_seteq: "A |\<subseteq>| B \<Longrightarrow> fcard B \<le> fcard A \<Longrightarrow> A = B"
by transfer (rule card_seteq)

lemma pfsubset_fcard_mono: "A |\<subset>| B \<Longrightarrow> fcard A < fcard B"
by transfer (rule psubset_card_mono)

lemma fcard_funion_finter: 
  "fcard A + fcard B = fcard (A |\<union>| B) + fcard (A |\<inter>| B)"
by transfer (rule card_Un_Int)

lemma fcard_funion_disjoint:
  "A |\<inter>| B = {||} \<Longrightarrow> fcard (A |\<union>| B) = fcard A + fcard B"
by transfer (rule card_Un_disjoint)

lemma fcard_funion_fsubset:
  "B |\<subseteq>| A \<Longrightarrow> fcard (A |-| B) = fcard A - fcard B"
by transfer (rule card_Diff_subset)

lemma diff_fcard_le_fcard_fminus:
  "fcard A - fcard B \<le> fcard(A |-| B)"
by transfer (rule diff_card_le_card_Diff)

lemma fcard_fminus1_less: "x |\<in>| A \<Longrightarrow> fcard (A |-| {|x|}) < fcard A"
by transfer (rule card_Diff1_less)

lemma fcard_fminus2_less:
  "x |\<in>| A \<Longrightarrow> y |\<in>| A \<Longrightarrow> fcard (A |-| {|x|} |-| {|y|}) < fcard A"
by transfer (rule card_Diff2_less)

lemma fcard_fminus1_le: "fcard (A |-| {|x|}) \<le> fcard A"
by transfer (rule card_Diff1_le)

lemma fcard_pfsubset: "A |\<subseteq>| B \<Longrightarrow> fcard A < fcard B \<Longrightarrow> A < B"
by transfer (rule card_psubset)

subsubsection {* ffold *}

(* FIXME: improve transferred to handle bounded meta quantification *)

context comp_fun_commute
begin
  lemmas ffold_empty[simp] = fold_empty[Transfer.transferred]

  lemma ffold_finsert [simp]:
    assumes "x |\<notin>| A"
    shows "ffold f z (finsert x A) = f x (ffold f z A)"
    using assms by (transfer fixing: f) (rule fold_insert)

  lemma ffold_fun_left_comm:
    "f x (ffold f z A) = ffold f (f x z) A"
    by (transfer fixing: f) (rule fold_fun_left_comm)

  lemma ffold_finsert2:
    "x |\<notin>| A \<Longrightarrow> ffold f z (finsert x A)  = ffold f (f x z) A"
    by (transfer fixing: f) (rule fold_insert2)

  lemma ffold_rec:
    assumes "x |\<in>| A"
    shows "ffold f z A = f x (ffold f z (A |-| {|x|}))"
    using assms by (transfer fixing: f) (rule fold_rec)
  
  lemma ffold_finsert_fremove:
    "ffold f z (finsert x A) = f x (ffold f z (A |-| {|x|}))"
     by (transfer fixing: f) (rule fold_insert_remove)
end

lemma ffold_fimage:
  assumes "inj_on g (fset A)"
  shows "ffold f z (g |`| A) = ffold (f \<circ> g) z A"
using assms by transfer' (rule fold_image)

lemma ffold_cong:
  assumes "comp_fun_commute f" "comp_fun_commute g"
  "\<And>x. x |\<in>| A \<Longrightarrow> f x = g x"
    and "s = t" and "A = B"
  shows "ffold f s A = ffold g t B"
using assms by transfer (metis Finite_Set.fold_cong)

context comp_fun_idem
begin

  lemma ffold_finsert_idem:
    "ffold f z (finsert x A)  = f x (ffold f z A)"
    by (transfer fixing: f) (rule fold_insert_idem)
  
  declare ffold_finsert [simp del] ffold_finsert_idem [simp]
  
  lemma ffold_finsert_idem2:
    "ffold f z (finsert x A) = ffold f (f x z) A"
    by (transfer fixing: f) (rule fold_insert_idem2)

end

subsection {* Choice in fsets *}

lemma fset_choice: 
  assumes "\<forall>x. x |\<in>| A \<longrightarrow> (\<exists>y. P x y)"
  shows "\<exists>f. \<forall>x. x |\<in>| A \<longrightarrow> P x (f x)"
  using assms by transfer metis

subsection {* Induction and Cases rules for fsets *}

lemma fset_exhaust [case_names empty insert, cases type: fset]:
  assumes fempty_case: "S = {||} \<Longrightarrow> P" 
  and     finsert_case: "\<And>x S'. S = finsert x S' \<Longrightarrow> P"
  shows "P"
  using assms by transfer blast

lemma fset_induct [case_names empty insert]:
  assumes fempty_case: "P {||}"
  and     finsert_case: "\<And>x S. P S \<Longrightarrow> P (finsert x S)"
  shows "P S"
proof -
  (* FIXME transfer and right_total vs. bi_total *)
  note Domainp_forall_transfer[transfer_rule]
  show ?thesis
  using assms by transfer (auto intro: finite_induct)
qed

lemma fset_induct_stronger [case_names empty insert, induct type: fset]:
  assumes empty_fset_case: "P {||}"
  and     insert_fset_case: "\<And>x S. \<lbrakk>x |\<notin>| S; P S\<rbrakk> \<Longrightarrow> P (finsert x S)"
  shows "P S"
proof -
  (* FIXME transfer and right_total vs. bi_total *)
  note Domainp_forall_transfer[transfer_rule]
  show ?thesis
  using assms by transfer (auto intro: finite_induct)
qed

lemma fset_card_induct:
  assumes empty_fset_case: "P {||}"
  and     card_fset_Suc_case: "\<And>S T. Suc (fcard S) = (fcard T) \<Longrightarrow> P S \<Longrightarrow> P T"
  shows "P S"
proof (induct S)
  case empty
  show "P {||}" by (rule empty_fset_case)
next
  case (insert x S)
  have h: "P S" by fact
  have "x |\<notin>| S" by fact
  then have "Suc (fcard S) = fcard (finsert x S)" 
    by transfer auto
  then show "P (finsert x S)" 
    using h card_fset_Suc_case by simp
qed

lemma fset_strong_cases:
  obtains "xs = {||}"
    | ys x where "x |\<notin>| ys" and "xs = finsert x ys"
by transfer blast

lemma fset_induct2:
  "P {||} {||} \<Longrightarrow>
  (\<And>x xs. x |\<notin>| xs \<Longrightarrow> P (finsert x xs) {||}) \<Longrightarrow>
  (\<And>y ys. y |\<notin>| ys \<Longrightarrow> P {||} (finsert y ys)) \<Longrightarrow>
  (\<And>x xs y ys. \<lbrakk>P xs ys; x |\<notin>| xs; y |\<notin>| ys\<rbrakk> \<Longrightarrow> P (finsert x xs) (finsert y ys)) \<Longrightarrow>
  P xsa ysa"
  apply (induct xsa arbitrary: ysa)
  apply (induct_tac x rule: fset_induct_stronger)
  apply simp_all
  apply (induct_tac xa rule: fset_induct_stronger)
  apply simp_all
  done

subsection {* Setup for Lifting/Transfer *}

subsubsection {* Relator and predicator properties *}

lift_definition fset_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> 'b fset \<Rightarrow> bool" is set_rel
parametric set_rel_transfer ..

lemma fset_rel_alt_def: "fset_rel R = (\<lambda>A B. (\<forall>x.\<exists>y. x|\<in>|A \<longrightarrow> y|\<in>|B \<and> R x y) 
  \<and> (\<forall>y. \<exists>x. y|\<in>|B \<longrightarrow> x|\<in>|A \<and> R x y))"
apply (rule ext)+
apply transfer'
apply (subst set_rel_def[unfolded fun_eq_iff]) 
by blast

lemma fset_rel_conversep: "fset_rel (conversep R) = conversep (fset_rel R)"
  unfolding fset_rel_alt_def by auto

lemmas fset_rel_eq [relator_eq] = set_rel_eq[Transfer.transferred]

lemma fset_rel_mono[relator_mono]: "A \<le> B \<Longrightarrow> fset_rel A \<le> fset_rel B"
unfolding fset_rel_alt_def by blast

lemma finite_set_rel:
  assumes fin: "finite X" "finite Z"
  assumes R_S: "set_rel (R OO S) X Z"
  shows "\<exists>Y. finite Y \<and> set_rel R X Y \<and> set_rel S Y Z"
proof -
  obtain f where f: "\<forall>x\<in>X. R x (f x) \<and> (\<exists>z\<in>Z. S (f x) z)"
  apply atomize_elim
  apply (subst bchoice_iff[symmetric])
  using R_S[unfolded set_rel_def OO_def] by blast
  
  obtain g where g: "\<forall>z\<in>Z. S (g z) z \<and> (\<exists>x\<in>X. R  x (g z))"
  apply atomize_elim
  apply (subst bchoice_iff[symmetric])
  using R_S[unfolded set_rel_def OO_def] by blast
  
  let ?Y = "f ` X \<union> g ` Z"
  have "finite ?Y" by (simp add: fin)
  moreover have "set_rel R X ?Y"
    unfolding set_rel_def
    using f g by clarsimp blast
  moreover have "set_rel S ?Y Z"
    unfolding set_rel_def
    using f g by clarsimp blast
  ultimately show ?thesis by metis
qed

lemma fset_rel_OO[relator_distr]: "fset_rel R OO fset_rel S = fset_rel (R OO S)"
apply (rule ext)+
by transfer (auto intro: finite_set_rel set_rel_OO[unfolded fun_eq_iff, rule_format, THEN iffD1])

lemma Domainp_fset[relator_domain]:
  assumes "Domainp T = P"
  shows "Domainp (fset_rel T) = (\<lambda>A. fBall A P)"
proof -
  from assms obtain f where f: "\<forall>x\<in>Collect P. T x (f x)"
    unfolding Domainp_iff[abs_def]
    apply atomize_elim
    by (subst bchoice_iff[symmetric]) auto
  from assms f show ?thesis
    unfolding fun_eq_iff fset_rel_alt_def Domainp_iff
    apply clarify
    apply (rule iffI)
      apply blast
    by (rename_tac A, rule_tac x="f |`| A" in exI, blast)
qed

lemmas reflp_fset_rel[reflexivity_rule] = reflp_set_rel[Transfer.transferred]

lemma right_total_fset_rel[transfer_rule]: "right_total A \<Longrightarrow> right_total (fset_rel A)"
unfolding right_total_def 
apply transfer
apply (subst(asm) choice_iff)
apply clarsimp
apply (rename_tac A f y, rule_tac x = "f ` y" in exI)
by (auto simp add: set_rel_def)

lemma left_total_fset_rel[reflexivity_rule]: "left_total A \<Longrightarrow> left_total (fset_rel A)"
unfolding left_total_def 
apply transfer
apply (subst(asm) choice_iff)
apply clarsimp
apply (rename_tac A f y, rule_tac x = "f ` y" in exI)
by (auto simp add: set_rel_def)

lemmas right_unique_fset_rel[transfer_rule] = right_unique_set_rel[Transfer.transferred]
lemmas left_unique_fset_rel[reflexivity_rule] = left_unique_set_rel[Transfer.transferred]

thm right_unique_fset_rel left_unique_fset_rel

lemma bi_unique_fset_rel[transfer_rule]: "bi_unique A \<Longrightarrow> bi_unique (fset_rel A)"
by (auto intro: right_unique_fset_rel left_unique_fset_rel iff: bi_unique_iff)

lemma bi_total_fset_rel[transfer_rule]: "bi_total A \<Longrightarrow> bi_total (fset_rel A)"
by (auto intro: right_total_fset_rel left_total_fset_rel iff: bi_total_iff)

lemmas fset_invariant_commute [invariant_commute] = set_invariant_commute[Transfer.transferred]

subsubsection {* Quotient theorem for the Lifting package *}

lemma Quotient_fset_map[quot_map]:
  assumes "Quotient R Abs Rep T"
  shows "Quotient (fset_rel R) (fimage Abs) (fimage Rep) (fset_rel T)"
  using assms unfolding Quotient_alt_def4
  by (simp add: fset_rel_OO[symmetric] fset_rel_conversep) (simp add: fset_rel_alt_def, blast)

subsubsection {* Transfer rules for the Transfer package *}

text {* Unconditional transfer rules *}

context
begin

interpretation lifting_syntax .

lemmas fempty_transfer [transfer_rule] = empty_transfer[Transfer.transferred]

lemma finsert_transfer [transfer_rule]:
  "(A ===> fset_rel A ===> fset_rel A) finsert finsert"
  unfolding fun_rel_def fset_rel_alt_def by blast

lemma funion_transfer [transfer_rule]:
  "(fset_rel A ===> fset_rel A ===> fset_rel A) funion funion"
  unfolding fun_rel_def fset_rel_alt_def by blast

lemma ffUnion_transfer [transfer_rule]:
  "(fset_rel (fset_rel A) ===> fset_rel A) ffUnion ffUnion"
  unfolding fun_rel_def fset_rel_alt_def by transfer (simp, fast)

lemma fimage_transfer [transfer_rule]:
  "((A ===> B) ===> fset_rel A ===> fset_rel B) fimage fimage"
  unfolding fun_rel_def fset_rel_alt_def by simp blast

lemma fBall_transfer [transfer_rule]:
  "(fset_rel A ===> (A ===> op =) ===> op =) fBall fBall"
  unfolding fset_rel_alt_def fun_rel_def by blast

lemma fBex_transfer [transfer_rule]:
  "(fset_rel A ===> (A ===> op =) ===> op =) fBex fBex"
  unfolding fset_rel_alt_def fun_rel_def by blast

(* FIXME transfer doesn't work here *)
lemma fPow_transfer [transfer_rule]:
  "(fset_rel A ===> fset_rel (fset_rel A)) fPow fPow"
  unfolding fun_rel_def
  using Pow_transfer[unfolded fun_rel_def, rule_format, Transfer.transferred]
  by blast

lemma fset_rel_transfer [transfer_rule]:
  "((A ===> B ===> op =) ===> fset_rel A ===> fset_rel B ===> op =)
    fset_rel fset_rel"
  unfolding fun_rel_def
  using set_rel_transfer[unfolded fun_rel_def,rule_format, Transfer.transferred, where A = A and B = B]
  by simp

lemma bind_transfer [transfer_rule]:
  "(fset_rel A ===> (A ===> fset_rel B) ===> fset_rel B) fbind fbind"
  using assms unfolding fun_rel_def
  using bind_transfer[unfolded fun_rel_def, rule_format, Transfer.transferred] by blast

text {* Rules requiring bi-unique, bi-total or right-total relations *}

lemma fmember_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(A ===> fset_rel A ===> op =) (op |\<in>|) (op |\<in>|)"
  using assms unfolding fun_rel_def fset_rel_alt_def bi_unique_def by metis

lemma finter_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(fset_rel A ===> fset_rel A ===> fset_rel A) finter finter"
  using assms unfolding fun_rel_def
  using inter_transfer[unfolded fun_rel_def, rule_format, Transfer.transferred] by blast

lemma fminus_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(fset_rel A ===> fset_rel A ===> fset_rel A) (op |-|) (op |-|)"
  using assms unfolding fun_rel_def
  using Diff_transfer[unfolded fun_rel_def, rule_format, Transfer.transferred] by blast

lemma fsubset_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(fset_rel A ===> fset_rel A ===> op =) (op |\<subseteq>|) (op |\<subseteq>|)"
  using assms unfolding fun_rel_def
  using subset_transfer[unfolded fun_rel_def, rule_format, Transfer.transferred] by blast

lemma fSup_transfer [transfer_rule]:
  "bi_unique A \<Longrightarrow> (set_rel (fset_rel A) ===> fset_rel A) Sup Sup"
  using assms unfolding fun_rel_def
  apply clarify
  apply transfer'
  using Sup_fset_transfer[unfolded fun_rel_def] by blast

(* FIXME: add right_total_fInf_transfer *)

lemma fInf_transfer [transfer_rule]:
  assumes "bi_unique A" and "bi_total A"
  shows "(set_rel (fset_rel A) ===> fset_rel A) Inf Inf"
  using assms unfolding fun_rel_def
  apply clarify
  apply transfer'
  using Inf_fset_transfer[unfolded fun_rel_def] by blast

lemma ffilter_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "((A ===> op=) ===> fset_rel A ===> fset_rel A) ffilter ffilter"
  using assms unfolding fun_rel_def
  using Lifting_Set.filter_transfer[unfolded fun_rel_def, rule_format, Transfer.transferred] by blast

lemma card_transfer [transfer_rule]:
  "bi_unique A \<Longrightarrow> (fset_rel A ===> op =) fcard fcard"
  using assms unfolding fun_rel_def
  using card_transfer[unfolded fun_rel_def, rule_format, Transfer.transferred] by blast

end

lifting_update fset.lifting
lifting_forget fset.lifting

end
