# begriffsschrift-in-lean
This is the mechanization of the propositional fragment of Frege's (1879) Begriﬀsschrift using the Lean theorem prover. In particular, our main goal is to formalize the independence proof of the formulas ¬¬A ≡ A, (A ⊃ B) ⊃ (B ⊃ A) ⊃ (A ≡ B), and ¬(A ≡ ¬B) ⊃ (A ≡ B) with respect to the axioms of Begriﬀsschrift developed by Duarte (2009, Appendix I).

We have defined the required formula and three-valued semantics using an inductive definition, and we have written the necessary axioms in the style of Hilbert. 'Alternative' document was a previous attempt, but we found a better method in 'valid' document that can replace general propositions (defined using open formulas and free variables). Therefore, we did not continue with 'alternative' and instead completed the entire proof in the context of open formulas in 'valid' document.

# References
[1] A. B. Duarte. L ́ogica e Aritm ́etica na Filosofia da Matem ́atica de Frege. PhD thesis, PUC-Rio, 2009.

[2] G. Frege. Conceptual Notation, and Related Articles. Translated [From the German] and Edited with a Biography and Introduction by Terrell Ward Bynum. Oxford University Press UK, Oxford, England, 1972.

[3] D. van Dalen. Logic and Structure. Springer Verlag, New York, 1980.
