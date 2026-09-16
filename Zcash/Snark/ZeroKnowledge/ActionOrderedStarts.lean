import Zcash.Snark.ZeroKnowledge.ActionOrderedSort
import Zcash.Snark.ZeroKnowledge.ActionOrderedPlacement
import Zcash.Snark.ZeroKnowledge.ActionOrderedRegionStarts

/-!
# Exact Action starts in source order

The checked legacy-sort order is the input to the 181-block placement certificate.
Restoring the original region indices then gives every one of the compiler's
395 starts, including both empty regions. No placement or ordering premise remains.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Halo2.FloorPlanner Zcash.Circuits.Action

/-- The source-indexed start rows computed by the actual V1 planner. -/
def actionRegionStartsCertificate : List ℕ :=
  [1768, 1770, 1762, 1763, 1764, 1769, 1773, 1772, 1758, 333, 751, 742, 332, 331, 1288, 1737, 1761, 330,
    700, 682, 329, 328, 1341, 1727, 1755, 334, 1773, 652, 325, 297, 917, 1713, 1750, 321, 721, 1664, 318,
    317, 1500, 1719, 1753, 313, 1770, 1767, 310, 309, 1076, 1731, 1757, 305, 1706, 1697, 303, 302, 1553,
    1743, 1747, 301, 1658, 1606, 300, 299, 864, 1741, 1752, 298, 670, 649, 296, 295, 970, 1733, 1759, 294,
    607, 604, 293, 292, 1129, 1721, 1760, 291, 613, 622, 290, 289, 1394, 1725, 1756, 288, 658, 661, 287,
    286, 1235, 1729, 1754, 285, 1776, 694, 284, 283, 1447, 1735, 1751, 282, 730, 733, 281, 280, 1182, 1739,
    1749, 279, 1615, 1627, 278, 277, 811, 1717, 1746, 276, 1667, 1676, 275, 274, 1023, 1723, 1748, 312,
    1709, 1755, 327, 314, 758, 1715, 1744, 319, 1761, 1758, 318, 317, 1235, 1731, 1746, 316, 1694, 1691,
    274, 275, 1023, 1723, 1657, 276, 1673, 1670, 277, 278, 970, 1713, 1739, 279, 1636, 1633, 280, 281, 1129,
    1715, 1740, 282, 1612, 1609, 283, 284, 1394, 1737, 1742, 285, 739, 736, 286, 287, 1500, 1735, 1743, 288,
    715, 712, 289, 290, 1553, 1733, 1750, 291, 691, 688, 292, 293, 1341, 1729, 1747, 294, 667, 664, 295,
    296, 758, 1727, 1748, 297, 643, 640, 298, 299, 1288, 1725, 1751, 300, 619, 616, 301, 302, 1447, 1721,
    1752, 303, 601, 598, 304, 305, 1182, 1717, 1753, 306, 610, 625, 307, 308, 1076, 1651, 1749, 320, 637,
    646, 329, 309, 917, 1643, 1754, 310, 697, 706, 311, 312, 864, 1647, 1741, 313, 1618, 1639, 314, 315,
    811, 1655, 757, 1642, 1658, 1691, 418, 1699, 1697, 272, 250, 1606, 273, 247, 1693, 524, 253, 1701, 673,
    1703, 1711, 304, 1700, 1703, 306, 307, 1764, 308, 333, 1689, 1606, 1685, 538, 381, 1709, 0, 311, 566,
    247, 1767, 0, 315, 655, 1688, 316, 319, 1685, 320, 1661, 745, 322, 323, 718, 324, 685, 326, 673, 634,
    247, 496, 1645, 631, 628, 325, 426, 1653, 503, 1687, 137, 1707, 468, 366, 351, 552, 256, 260, 268, 266,
    269, 586, 580, 596, 594, 582, 0, 1766, 1765, 1771, 321, 676, 679, 322, 323, 703, 324, 709, 724, 325,
    326, 727, 327, 748, 328, 754, 1621, 273, 510, 1719, 1624, 1630, 299, 454, 1649, 588, 1695, 137, 1705,
    482, 411, 396, 440, 258, 262, 270, 264, 271, 592, 590, 597, 588, 584, 1745, 1681]

set_option maxRecDepth 4096 in
/-- The exact sorted records have precisely the shapes covered by the placement certificate. -/
theorem actionSortedRegionShapes_summaries :
    actionSortedRegionShapes.map RegionShape.toSummary = actionSortedPlacementShapes := by
  kernel_rfl

set_option maxRecDepth 4096 in
/-- Sorting the certified placement pairs by region index recovers the original-order starts used by
synthesis. -/
private theorem restoreIndexOrder :
    (V1.sortPairsByIndex (actionSortedRegionIndices.zip actionSortedPlacementStarts)).map Prod.snd =
      actionRegionStartsCertificate := by
  kernel_rfl

/-- A proved sort order and placement result determine the candidate start list, connecting local
certificates to the planner. -/
private theorem planCandidate_starts_of_pairs
    (shapes sorted : List RegionShape) (pairs : List (ℕ × ℕ))
    (hsort : (Pdqsort.quicksort shapes.toArray (fun left right => left.key < right.key)).reverse.toList = sorted)
    (hslot : (slotIn sorted).1 = pairs) :
    (V1.planCandidate shapes).1 = (V1.sortPairsByIndex pairs).map Prod.snd := by
  simp only [V1.planCandidate, hsort, hslot]

/-- The finite source planner computes the certified start rows without additional premises. -/
theorem actionOrderedRegionStarts_eq_certificate :
    actionOrderedRegionStarts = actionRegionStartsCertificate := by
  have hstarts := (congrArg
    (fun summaries => (slotShapeSummariesFrom summaries ∅).1)
      actionSortedRegionShapes_summaries).trans actionSortedPlacementStarts_eq_slot
  have hpairs := (slotIn_pairs_eq_zip actionSortedRegionShapes).trans
    (congrArg₂ List.zip actionSortedRegionShapes_indices hstarts)
  exact actionOrderedRegionStarts_def.trans
    ((planCandidate_starts_of_pairs _ _ _ actionOrderedRegionShapes_sorted hpairs).trans restoreIndexOrder)

/-- The actual Action compiler uses those same source-indexed rows. -/
theorem actionCircuit_regionStarts_eq_certificate :
    actionCircuit.regionStarts = actionRegionStartsCertificate :=
  actionCircuit_regionStarts_eq_ordered.trans actionOrderedRegionStarts_eq_certificate

end Zcash.Snark.ZeroKnowledge
