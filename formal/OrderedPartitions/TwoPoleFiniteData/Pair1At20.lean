import OrderedPartitions.TwoPoleFiniteBrackets
import OrderedPartitions.TwoPoleFiniteData.Table

namespace OrderedPartitions.TwoPoleFinite

set_option maxHeartbeats 0
set_option maxRecDepth 65536


private def lowerBoxes : Boxes := [(-509/3,-1017/7), (-965/59,-241/15), (-869/155,-217/39), (-745/279,-93/35), (-611/413,-305/207), (-485/539,-121/135), (-95/161,-379/645), (-301/723,-75/181), (-31/97,-247/777), (-109/403,-217/807)]
private def upperBoxes : Boxes := [(-125/3,-999/25), (-931/93,-465/47), (-827/197,-413/99), (-703/321,-351/161), (-575/449,-287/225), (-459/565,-229/283), (-91/165,-363/661), (-73/183,-291/733), (-61/195,-243/781), (-217/807,-27/101)]

theorem checkedPair1At20 : RootTracking.OrderedPair 10 (row 20 2) (row 21 2) := by
  apply stay_pair (B:=lowerBoxes) (C:=upperBoxes) checkedTable (by decide) (by decide) (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

end OrderedPartitions.TwoPoleFinite
