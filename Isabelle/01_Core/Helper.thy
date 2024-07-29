theory Helper
  imports Main 
begin
section ‹Helper for top›


theorem list_comp_prop_1: "∀p. [p i. i ← [0..((int (Suc n)))]] = [p i. i ← [0..(int n)]] @ [p ((int (Suc n)))]"
    apply (induction n)
    apply (simp add: upto_rec2)
  by (simp add: upto_rec2)

end