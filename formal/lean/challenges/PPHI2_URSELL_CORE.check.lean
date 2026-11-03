-- 本文件由 `python tools/lean_challenge.py --init` 生成，请勿手改；要改陈述请改注册表并重跑。
-- 节点: PPHI2_URSELL_CORE
-- 本文件只含「陈述冻结 + 公理足迹」，不含任何证明。
import S6Isserlis.UrsellCore
import S6Isserlis.UrsellSplit
import S6Isserlis.UrsellGeneral
import S6Isserlis.UrsellConnected
import S6Isserlis.UrsellThm32

#check @Pphi2Ursell.isCompatible_union_iff
#print axioms Pphi2Ursell.isCompatible_union_iff
#check @Pphi2Ursell.ursell_empty
#print axioms Pphi2Ursell.ursell_empty
#check @Pphi2Ursell.ursell_singleton
#print axioms Pphi2Ursell.ursell_singleton
#check @Pphi2Ursell.ursell_pair_eq_neg_one
#print axioms Pphi2Ursell.ursell_pair_eq_neg_one
#check @Pphi2Ursell.compatInd_eq_sum
#print axioms Pphi2Ursell.compatInd_eq_sum
#check @Pphi2Ursell.ursell_eq_zero_of_compatible
#print axioms Pphi2Ursell.ursell_eq_zero_of_compatible
#check @Pphi2Ursell.compatInd_singleton
#print axioms Pphi2Ursell.compatInd_singleton
#check @Pphi2Ursell.compatInd_union
#print axioms Pphi2Ursell.compatInd_union
#check @Pphi2Ursell.ursell_union_singleton_eq_zero
#print axioms Pphi2Ursell.ursell_union_singleton_eq_zero
#check @Pphi2Ursell.ursell_union_eq_zero_of_isCompatible_right
#print axioms Pphi2Ursell.ursell_union_eq_zero_of_isCompatible_right
#check @Pphi2Ursell.sum_powerset_union
#print axioms Pphi2Ursell.sum_powerset_union
#check @Pphi2Ursell.sdiff_union_sdiff
#print axioms Pphi2Ursell.sdiff_union_sdiff
#check @Pphi2Ursell.compatInd_sdiff_union_sdiff
#print axioms Pphi2Ursell.compatInd_sdiff_union_sdiff
#check @Pphi2Ursell.ursell_eq_zero_of_split
#print axioms Pphi2Ursell.ursell_eq_zero_of_split
#check @Pphi2Ursell.edgeWithin
#print axioms Pphi2Ursell.edgeWithin
#check @Pphi2Ursell.connSum
#print axioms Pphi2Ursell.connSum
#check @Pphi2Ursell.connSum_eq_zero_of_isCompatible
#print axioms Pphi2Ursell.connSum_eq_zero_of_isCompatible
#check @Pphi2Ursell.edgeWithin_eq_empty_iff
#print axioms Pphi2Ursell.edgeWithin_eq_empty_iff
#check @Pphi2Ursell.sum_neg_one_pow_card_edgeWithin
#print axioms Pphi2Ursell.sum_neg_one_pow_card_edgeWithin
#check @Pphi2Ursell.connSum_singleton
#print axioms Pphi2Ursell.connSum_singleton
#check @Pphi2Ursell.edgeWithin_mono
#print axioms Pphi2Ursell.edgeWithin_mono
#check @Pphi2Ursell.edgeWithin_disjoint
#print axioms Pphi2Ursell.edgeWithin_disjoint
#check @Pphi2Ursell.edgeWithin_union_subset
#print axioms Pphi2Ursell.edgeWithin_union_subset
#check @Pphi2Ursell.card_edgeWithin_union
#print axioms Pphi2Ursell.card_edgeWithin_union
#check @Pphi2Ursell.neg_one_pow_card_union
#print axioms Pphi2Ursell.neg_one_pow_card_union
#check @Pphi2Ursell.compatInd_eq_sum_connSum_of_isCompatible
#print axioms Pphi2Ursell.compatInd_eq_sum_connSum_of_isCompatible
#check @Pphi2Ursell.edgeWithin_union_eq
#print axioms Pphi2Ursell.edgeWithin_union_eq
#check @Pphi2Ursell.connSum_empty
#print axioms Pphi2Ursell.connSum_empty
#check @Pphi2Ursell.reachSet
#print axioms Pphi2Ursell.reachSet
#check @Pphi2Ursell.mem_reachSet
#print axioms Pphi2Ursell.mem_reachSet
#check @Pphi2Ursell.reachSet_subset
#print axioms Pphi2Ursell.reachSet_subset
#check @Pphi2Ursell.subset_edgeWithin_union_of_reachSet
#print axioms Pphi2Ursell.subset_edgeWithin_union_of_reachSet
#check @Pphi2Ursell.reachSet_inter_edgeWithin_eq
#print axioms Pphi2Ursell.reachSet_inter_edgeWithin_eq
#check @Pphi2Ursell.connected_induce_reachSet
#print axioms Pphi2Ursell.connected_induce_reachSet
#check @Pphi2Ursell.connected_induce_inter_edgeWithin
#print axioms Pphi2Ursell.connected_induce_inter_edgeWithin
#check @Pphi2Ursell.eq_inter_union_inter_sdiff
#print axioms Pphi2Ursell.eq_inter_union_inter_sdiff
#check @Pphi2Ursell.ofComponents_toComponents
#print axioms Pphi2Ursell.ofComponents_toComponents
#check @Pphi2Ursell.reachSet_ofComponents
#print axioms Pphi2Ursell.reachSet_ofComponents
#check @Pphi2Ursell.mem_compIndex
#print axioms Pphi2Ursell.mem_compIndex
#check @Pphi2Ursell.pairingSum_eq_sum_connSum_mul
#print axioms Pphi2Ursell.pairingSum_eq_sum_connSum_mul
#check @Pphi2Ursell.sum_neg_one_pow_eq_pairingSum
#print axioms Pphi2Ursell.sum_neg_one_pow_eq_pairingSum
#check @Pphi2Ursell.compatInd_eq_sum_connSum
#print axioms Pphi2Ursell.compatInd_eq_sum_connSum
#check @Pphi2Ursell.ursell_eq_connSum
#print axioms Pphi2Ursell.ursell_eq_connSum
#check @Pphi2Ursell.eq_edgeWithin_of_connected_of_isTree
#print axioms Pphi2Ursell.eq_edgeWithin_of_connected_of_isTree
#check @Pphi2Ursell.connSum_eq_neg_one_pow_of_isTree
#print axioms Pphi2Ursell.connSum_eq_neg_one_pow_of_isTree
#check @Pphi2Ursell.connSum_singleton_ne_zero
#print axioms Pphi2Ursell.connSum_singleton_ne_zero
#check @Pphi2Ursell.sum_with_edge_eq_neg_sum_without
#print axioms Pphi2Ursell.sum_with_edge_eq_neg_sum_without
#check @Pphi2Ursell.connected_spanning_insert
#print axioms Pphi2Ursell.connected_spanning_insert
#check @Pphi2Ursell.reachable_deleteEdges_iff
#print axioms Pphi2Ursell.reachable_deleteEdges_iff
#check @Pphi2Ursell.deleteEdges_fromEdgeSet_singleton
#print axioms Pphi2Ursell.deleteEdges_fromEdgeSet_singleton
#check @Pphi2Ursell.connected_spanning_erase_of_not_isBridge
#print axioms Pphi2Ursell.connected_spanning_erase_of_not_isBridge
#check @Pphi2Ursell.union_singleton_roundtrip
#print axioms Pphi2Ursell.union_singleton_roundtrip
#check @Pphi2Ursell.union_singleton_connected_not_bridge
#print axioms Pphi2Ursell.union_singleton_connected_not_bridge
#check @Pphi2Ursell.sum_neg_one_pow_of_not_bridge_eq_zero
#print axioms Pphi2Ursell.sum_neg_one_pow_of_not_bridge_eq_zero
#check @Pphi2Ursell.connSum_eq_sum_of_isBridge
#print axioms Pphi2Ursell.connSum_eq_sum_of_isBridge
#check @Pphi2Ursell.not_reachable_of_isBridge
#print axioms Pphi2Ursell.not_reachable_of_isBridge
#check @Pphi2Ursell.not_mem_reachSet_of_isBridge
#print axioms Pphi2Ursell.not_mem_reachSet_of_isBridge
#check @Pphi2Ursell.mem_of_connected_of_isBridge
#print axioms Pphi2Ursell.mem_of_connected_of_isBridge
#check @Pphi2Ursell.cross_edge_eq_bridge
#print axioms Pphi2Ursell.cross_edge_eq_bridge
#check @Pphi2Ursell.sideOf
#print axioms Pphi2Ursell.sideOf
#check @Pphi2Ursell.sideOf_union_sdiff
#print axioms Pphi2Ursell.sideOf_union_sdiff
#check @Pphi2Ursell.mem_sideOf_self
#print axioms Pphi2Ursell.mem_sideOf_self
#check @Pphi2Ursell.not_cross_of_mem_of_connected
#print axioms Pphi2Ursell.not_cross_of_mem_of_connected
#check @Pphi2Ursell.edgeGraph
#print axioms Pphi2Ursell.edgeGraph
#check @Pphi2Ursell.sideOf_of_mem_edge
#print axioms Pphi2Ursell.sideOf_of_mem_edge
#check @Pphi2Ursell.sideOf_step_same
#print axioms Pphi2Ursell.sideOf_step_same
#check @Pphi2Ursell.not_mem_sideOf_b
#print axioms Pphi2Ursell.not_mem_sideOf_b
#check @Pphi2Ursell.not_iff_sideOf_of_eq
#print axioms Pphi2Ursell.not_iff_sideOf_of_eq
#check @Pphi2Ursell.count_bridge_even_iff_same_side
#print axioms Pphi2Ursell.count_bridge_even_iff_same_side
#check @Pphi2Ursell.bridge_notMem_edges_of_isPath
#print axioms Pphi2Ursell.bridge_notMem_edges_of_isPath
#check @Pphi2Ursell.reachable_filter_of_walk_aux
#print axioms Pphi2Ursell.reachable_filter_of_walk_aux
#check @Pphi2Ursell.connected_induce_filter_sideOf
#print axioms Pphi2Ursell.connected_induce_filter_sideOf
#check @Pphi2Ursell.connected_induce_filter_sideOf_b
#print axioms Pphi2Ursell.connected_induce_filter_sideOf_b
#check @Pphi2Ursell.disjoint_filter_sideOf
#print axioms Pphi2Ursell.disjoint_filter_sideOf
#check @Pphi2Ursell.connected_union_bridge
#print axioms Pphi2Ursell.connected_union_bridge
#check @Pphi2Ursell.card_eq_card_filter_add_card_filter_add_one
#print axioms Pphi2Ursell.card_eq_card_filter_add_card_filter_add_one
#check @Pphi2Ursell.neg_one_pow_card_eq_neg_mul
#print axioms Pphi2Ursell.neg_one_pow_card_eq_neg_mul
#check @Pphi2Ursell.sideOf_subset
#print axioms Pphi2Ursell.sideOf_subset
#check @Pphi2Ursell.sdiff_sideOf_subset
#print axioms Pphi2Ursell.sdiff_sideOf_subset
#check @Pphi2Ursell.mem_edgeWithin_sideOf_or_eq
#print axioms Pphi2Ursell.mem_edgeWithin_sideOf_or_eq
#check @Pphi2Ursell.disjoint_edgeWithin_sideOf
#print axioms Pphi2Ursell.disjoint_edgeWithin_sideOf
#check @Pphi2Ursell.edgeWithin_union_sideOf_eq
#print axioms Pphi2Ursell.edgeWithin_union_sideOf_eq
#check @Pphi2Ursell.not_mem_edgeWithin_sideOf_b
#print axioms Pphi2Ursell.not_mem_edgeWithin_sideOf_b
#check @Pphi2Ursell.not_mem_edgeWithin_sdiff_sideOf
#print axioms Pphi2Ursell.not_mem_edgeWithin_sdiff_sideOf
#check @Pphi2Ursell.edgeWithin_sdiff_eq_union
#print axioms Pphi2Ursell.edgeWithin_sdiff_eq_union
#check @Pphi2Ursell.mem_filter_sideOf_of_mem_sdiff
#print axioms Pphi2Ursell.mem_filter_sideOf_of_mem_sdiff
#check @Pphi2Ursell.powerset_eq_filter_insert
#print axioms Pphi2Ursell.powerset_eq_filter_insert
#check @Pphi2Ursell.subset_sdiff_of_not_mem
#print axioms Pphi2Ursell.subset_sdiff_of_not_mem
#check @Pphi2Ursell.eq_singleton_union_filter_sideOf
#print axioms Pphi2Ursell.eq_singleton_union_filter_sideOf
#check @Pphi2Ursell.not_connected_of_not_mem_bridge
#print axioms Pphi2Ursell.not_connected_of_not_mem_bridge
#check @Pphi2Ursell.connSum_eq_sum_filter_mem_bridge
#print axioms Pphi2Ursell.connSum_eq_sum_filter_mem_bridge
#check @Pphi2Ursell.filter_sideOf_subset_edgeWithin
#print axioms Pphi2Ursell.filter_sideOf_subset_edgeWithin
#check @Pphi2Ursell.union_filter_sideOf_eq
#print axioms Pphi2Ursell.union_filter_sideOf_eq
#check @Pphi2Ursell.filter_union_filter_eq_of_subset
#print axioms Pphi2Ursell.filter_union_filter_eq_of_subset
#check @Pphi2Ursell.filter_sdiff_sideOf_subset_edgeWithin
#print axioms Pphi2Ursell.filter_sdiff_sideOf_subset_edgeWithin
#check @Pphi2Ursell.sideOf_b_subset_sdiff_sideOf_a
#print axioms Pphi2Ursell.sideOf_b_subset_sdiff_sideOf_a
#check @Pphi2Ursell.sideOf_a_subset_sdiff_sideOf_b
#print axioms Pphi2Ursell.sideOf_a_subset_sdiff_sideOf_b
#check @Pphi2Ursell.mem_sideOf_iff_reachable
#print axioms Pphi2Ursell.mem_sideOf_iff_reachable
#check @Pphi2Ursell.sideOf_b_of_mem_edge
#print axioms Pphi2Ursell.sideOf_b_of_mem_edge
#check @Pphi2Ursell.mem_sideOf_a_or_mem_sideOf_b_of_reachable
#print axioms Pphi2Ursell.mem_sideOf_a_or_mem_sideOf_b_of_reachable
#check @Pphi2Ursell.sdiff_sideOf_a_subset_sideOf_b
#print axioms Pphi2Ursell.sdiff_sideOf_a_subset_sideOf_b
#check @Pphi2Ursell.sideOf_union_sideOf_eq
#print axioms Pphi2Ursell.sideOf_union_sideOf_eq
#check @Pphi2Ursell.sdiff_sideOf_a_eq_sideOf_b
#print axioms Pphi2Ursell.sdiff_sideOf_a_eq_sideOf_b
#check @Pphi2Ursell.connected_induce_edgeGraph_of_connected
#print axioms Pphi2Ursell.connected_induce_edgeGraph_of_connected
#check @Pphi2Ursell.connected_filter_sideOf_of_connected
#print axioms Pphi2Ursell.connected_filter_sideOf_of_connected
#check @Pphi2Ursell.connected_of_connected_filter_sideOf
#print axioms Pphi2Ursell.connected_of_connected_filter_sideOf
#check @Pphi2Ursell.ite_connected_mul_sign_eq_neg_mul
#print axioms Pphi2Ursell.ite_connected_mul_sign_eq_neg_mul
#check @Pphi2Ursell.filter_pair_union_eq_self
#print axioms Pphi2Ursell.filter_pair_union_eq_self
#check @Pphi2Ursell.filter_pair_union_filter_eq_self
#print axioms Pphi2Ursell.filter_pair_union_filter_eq_self
#check @Pphi2Ursell.sum_filter_mem_bridge_eq_sum_pairs
#print axioms Pphi2Ursell.sum_filter_mem_bridge_eq_sum_pairs
#check @Pphi2Ursell.sum_pairs_eq_sum_sum
#print axioms Pphi2Ursell.sum_pairs_eq_sum_sum
#check @Pphi2Ursell.connSum_eq_neg_mul_connSum_connSum
#print axioms Pphi2Ursell.connSum_eq_neg_mul_connSum_connSum
#check @Pphi2Ursell.card_sideOf_lt
#print axioms Pphi2Ursell.card_sideOf_lt
#check @Pphi2Ursell.card_sdiff_sideOf_lt
#print axioms Pphi2Ursell.card_sdiff_sideOf_lt
#check @Pphi2Ursell.connSum_ne_zero_of_isBridge
#print axioms Pphi2Ursell.connSum_ne_zero_of_isBridge
#check @Pphi2Ursell.filter_union_filter_eq_sdiff
#print axioms Pphi2Ursell.filter_union_filter_eq_sdiff
#check @Pphi2Ursell.mem_sideOf_of_walk
#print axioms Pphi2Ursell.mem_sideOf_of_walk
