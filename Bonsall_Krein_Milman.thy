(*  Title:      Bonsall_Krein_Milman.thy
    Author:     Christopher Hoskin
*)

section \<open>Bonsall Krein-Milman Theorem\<close>

text \<open> From my notes, 21-Aug 2011 \<close>

theory Bonsall_Krein_Milman
  imports "HOL-Analysis.Polytope" "HOL-Hahn_Banach.Subspace" "HOL-Hahn_Banach.Linearform"
begin

text \<open>Given a set of objects of the same type such that the set is closed under minus, plus, zero 
and uminus (and scalar multiplication?) a map from the set to the real numbers is said to be 
subadditive if it is homogenous for positive scalars and addition satisfies a triangle inequality. \<close>

(* 
The following definition is motivated by the definition of seminorm in Hahn_Banach/Normed_Space.
Scalar \<cdot> multiplication is defined in Hahn_Banach/Vector_Space.
*)

locale subadditive =
  fixes A :: "'a::{minus, plus, zero, uminus} set"
  fixes subadditive :: "'a \<Rightarrow> real"    ("\<parallel>_\<parallel>")
  assumes positive_homogenous [iff?]: "x \<in> A \<Longrightarrow> \<parallel>a \<cdot> x\<parallel> = \<bar>a\<bar> * \<parallel>x\<parallel>"
    and subadditive [iff?]: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> \<parallel>x + y\<parallel> \<le> \<parallel>x\<parallel> + \<parallel>y\<parallel>"

(*
Need to show set of functions from a set to a real vector space forms a vector space.
Approach adopted from treatment of bcontfun in Analysis/Bounded_Continuous_Function
*)

definition "algdual = {f. linearform UNIV f}"

typedef (overloaded) ('a,'b) algdual ("(_ \<Rightarrow>\<^sub>L /_)" [22, 21] 21) =
  "algdual::('a::{minus,plus,uminus,zero}  \<Rightarrow> real) set"

instantiation algdual :: (set, real) real_vector
begin
end
  


(*
 The following is definition is inspired by the definition of norm_pres_extensions in
 Hahn_Banach/Function_Order.
*)

definition
  dominated_functionals ::
   "'a::{plus,minus,uminus,zero} set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow>  ('a \<Rightarrow> real)  set"
   where
  "dominated_functionals B p
    = {x. (\<forall>b \<in> B. x b \<le> p b) \<and> linearform B x}"

(* convex is defined as convex :: "'a::real_vector set \<Rightarrow> bool" in Convex_Euclidean_Space *)

lemma (in subadditive) dom_convex:
  fixes B
  assumes "vectorspace A" "subspace B A"
  shows "convex (dominated_functionals B p)"

(* proposition Bonsall_Krein_Milman:*)
  
end

