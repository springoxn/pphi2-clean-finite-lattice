-- 本文件由 `python tools/lean_challenge.py --init` 生成，请勿手改；要改陈述请改注册表并重跑。
-- 节点: PPHI2_WICK_FINITE_DIM
-- 本文件只含「陈述冻结 + 公理足迹」，不含任何证明。
import S6Isserlis.Wick
import S6Isserlis.HermiteDeriv
import S6Isserlis.WickBridge

#check @Wick.wick_zero
#print axioms Wick.wick_zero
#check @Wick.wick_one
#print axioms Wick.wick_one
#check @Wick.wick_add_two
#print axioms Wick.wick_add_two
#check @Wick.wick_two
#print axioms Wick.wick_two
#check @Wick.wick_three
#print axioms Wick.wick_three
#check @Wick.wick_four
#print axioms Wick.wick_four
#check @Wick.natDegree_wick_le
#print axioms Wick.natDegree_wick_le
#check @Polynomial.derivative_hermite
#print axioms Polynomial.derivative_hermite
#check @WickBridge.wick_eq_hermite
#print axioms WickBridge.wick_eq_hermite
