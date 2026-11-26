import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-125/3,-1999/49), (-1861/187,-465/47), (-1653/395,-413/99), (-1405/643,-351/161), (-575/449,-1149/899), (-459/565,-917/1131), (-727/1321,-363/661), (-73/183,-583/1465), (-61/195,-487/1561), (-217/807,-433/1615)]
private def upperBoxes : Boxes := [(-2037/11,-509/3), (-975/49,-1949/99), (-1787/261,-893/131), (-785/239,-1569/479), (-83/45,-1327/721), (-17/15,-1087/961), (-873/1175,-109/147), (-699/1349,-349/675), (-569/1479,-71/185), (-241/783,-481/1567), (-433/1615,-27/101)]

theorem checkedPair1At21 : RootTracking.OrderedPair 10 (row 21 2) (row 22 2) := by
  apply rise_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
