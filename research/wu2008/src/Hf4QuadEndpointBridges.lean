import Hf4QuadPanel0
import Hf4QuadBatch0
import Hf4QuadBatch1
import Hf4QuadBatch2
import Hf4QuadBatch3
import Hf4QuadBatch4
import Hf4QuadBatch5
import Hf4QuadBatch6
import Hf4QuadBatch7
import Hf4QuadBatch8
import Hf4QuadBatch9
import Hf4QuadBatch10
import Hf4QuadBatch11
import Hf4QuadBatch12
import Hf4QuadCompactIntegral

noncomputable section

namespace Hf4Quad.Panel0
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((17511388157/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass 1 (21/20) ∧
    SigmaActualBlockSeparable.endpointCellMass 1 (21/20) ≤ (21990320141/6000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(41/40)-(1/40)) (by norm_num : ((41/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel0

namespace Hf4Quad.Panel1
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((42735154237/2000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (21/20) (11/10) ∧
    SigmaActualBlockSeparable.endpointCellMass (21/20) (11/10) ≤ (44167542079/2000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(43/40)-(1/40)) (by norm_num : ((43/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel1

namespace Hf4Quad.Panel2
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((54983970103/1000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (11/10) (23/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (11/10) (23/20) ≤ (27828694777/500000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(9/8)-(1/40)) (by norm_num : ((9/8):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel2

namespace Hf4Quad.Panel3
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((75615759727/750000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (23/20) (6/5) ∧
    SigmaActualBlockSeparable.endpointCellMass (23/20) (6/5) ≤ (304339421431/3000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(47/40)-(1/40)) (by norm_num : ((47/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel3

namespace Hf4Quad.Panel4
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((234731806523/1500000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (6/5) (5/4) ∧
    SigmaActualBlockSeparable.endpointCellMass (6/5) (5/4) ≤ (117798272821/750000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(49/40)-(1/40)) (by norm_num : ((49/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel4

namespace Hf4Quad.Panel5
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((1320201268963/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (5/4) (13/10) ∧
    SigmaActualBlockSeparable.endpointCellMass (5/4) (13/10) ≤ (1323374584873/6000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(51/40)-(1/40)) (by norm_num : ((51/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel5

namespace Hf4Quad.Panel6
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((869573851603/3000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (13/10) (27/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (13/10) (27/20) ≤ (435512932469/1500000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(53/40)-(1/40)) (by norm_num : ((53/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel6

namespace Hf4Quad.Panel7
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((1093929758717/3000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (27/20) (7/5) ∧
    SigmaActualBlockSeparable.endpointCellMass (27/20) (7/5) ≤ (1095256637681/3000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(11/8)-(1/40)) (by norm_num : ((11/8):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel7

namespace Hf4Quad.Panel8
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((2659799257229/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (7/5) (29/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (7/5) (29/20) ≤ (106488928679/240000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(57/40)-(1/40)) (by norm_num : ((57/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel8

namespace Hf4Quad.Panel9
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((314954555417/600000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (29/20) (3/2) ∧
    SigmaActualBlockSeparable.endpointCellMass (29/20) (3/2) ≤ (787939918763/1500000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(59/40)-(1/40)) (by norm_num : ((59/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel9

namespace Hf4Quad.Panel10
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((1217530203413/2000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (3/2) (31/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (3/2) (31/20) ≤ (1218204654199/2000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(61/40)-(1/40)) (by norm_num : ((61/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel10

namespace Hf4Quad.Panel11
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((4165178758679/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (31/20) (8/5) ∧
    SigmaActualBlockSeparable.endpointCellMass (31/20) (8/5) ≤ (4167029268029/6000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(63/40)-(1/40)) (by norm_num : ((63/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel11

namespace Hf4Quad.Panel12
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((4684176470717/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (8/5) (33/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (8/5) (33/20) ≤ (937174127203/1200000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(13/8)-(1/40)) (by norm_num : ((13/8):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel12

namespace Hf4Quad.Panel13
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((5206966839587/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (33/20) (17/10) ∧
    SigmaActualBlockSeparable.endpointCellMass (33/20) (17/10) ≤ (1041703925701/1200000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(67/40)-(1/40)) (by norm_num : ((67/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel13

namespace Hf4Quad.Panel14
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((5731363703357/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (17/10) (7/4) ∧
    SigmaActualBlockSeparable.endpointCellMass (17/10) (7/4) ≤ (5732788793351/6000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(69/40)-(1/40)) (by norm_num : ((69/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel14

namespace Hf4Quad.Panel15
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((6255541384729/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (7/4) (9/5) ∧
    SigmaActualBlockSeparable.endpointCellMass (7/4) (9/5) ≤ (6256850842267/6000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(71/40)-(1/40)) (by norm_num : ((71/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel15

namespace Hf4Quad.Panel16
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((564831380779/500000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (9/5) (37/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (9/5) (37/20) ≤ (564931775211/500000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(73/40)-(1/40)) (by norm_num : ((73/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel16

namespace Hf4Quad.Panel17
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((3648700217911/3000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (37/20) (19/10) ∧
    SigmaActualBlockSeparable.endpointCellMass (37/20) (19/10) ≤ (3649255214407/3000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(15/8)-(1/40)) (by norm_num : ((15/8):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel17

namespace Hf4Quad.Panel18
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((976594892569/750000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (19/10) (39/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (19/10) (39/20) ≤ (3906891603151/3000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(77/40)-(1/40)) (by norm_num : ((77/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel18

namespace Hf4Quad.Panel19
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((4161590251993/3000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (39/20) 2 ∧
    SigmaActualBlockSeparable.endpointCellMass (39/20) 2 ≤ (4162063361221/3000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(79/40)-(1/40)) (by norm_num : ((79/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel19

namespace Hf4Quad.Panel20
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((8827946374543/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass 2 (41/20) ∧
    SigmaActualBlockSeparable.endpointCellMass 2 (41/20) ≤ (8828821822639/6000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(81/40)-(1/40)) (by norm_num : ((81/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel20

namespace Hf4Quad.Panel21
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((777205780931/500000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (41/20) (21/10) ∧
    SigmaActualBlockSeparable.endpointCellMass (41/20) (21/10) ≤ (194318339979/125000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(83/40)-(1/40)) (by norm_num : ((83/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel21

namespace Hf4Quad.Panel22
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((654551533467/400000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (21/10) (43/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (21/10) (43/20) ≤ (3273008426327/2000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(17/8)-(1/40)) (by norm_num : ((17/8):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel22

namespace Hf4Quad.Panel23
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((10302975706067/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (43/20) (11/5) ∧
    SigmaActualBlockSeparable.endpointCellMass (43/20) (11/5) ≤ (10303674263243/6000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(87/40)-(1/40)) (by norm_num : ((87/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel23

namespace Hf4Quad.Panel24
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((1796712675513/1000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (11/5) (9/4) ∧
    SigmaActualBlockSeparable.endpointCellMass (11/5) (9/4) ≤ (449205237451/250000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(89/40)-(1/40)) (by norm_num : ((89/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel24

namespace Hf4Quad.Panel25
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((2812485416669/1500000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (9/4) (23/10) ∧
    SigmaActualBlockSeparable.endpointCellMass (9/4) (23/10) ≤ (1125054642059/600000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(91/40)-(1/40)) (by norm_num : ((91/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel25

namespace Hf4Quad.Panel26
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((2927949619921/1500000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (23/10) (47/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (23/10) (47/20) ≤ (5856181034321/3000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(93/40)-(1/40)) (by norm_num : ((93/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel26

namespace Hf4Quad.Panel27
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((6082861207903/3000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (47/20) (12/5) ∧
    SigmaActualBlockSeparable.endpointCellMass (47/20) (12/5) ≤ (6083124147787/3000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(19/8)-(1/40)) (by norm_num : ((19/8):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel27

namespace Hf4Quad.Panel28
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((4203877263587/2000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (12/5) (49/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (12/5) (49/20) ≤ (4204041049541/2000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(97/40)-(1/40)) (by norm_num : ((97/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel28

namespace Hf4Quad.Panel29
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((13049481354647/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (49/20) (5/2) ∧
    SigmaActualBlockSeparable.endpointCellMass (49/20) (5/2) ≤ (13049941004429/6000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(99/40)-(1/40)) (by norm_num : ((99/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel29

namespace Hf4Quad.Panel30
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((2695851347101/1200000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (5/2) (51/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (5/2) (51/20) ≤ (13479686861231/6000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(101/40)-(1/40)) (by norm_num : ((101/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel30

namespace Hf4Quad.Panel31
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((1737621129151/750000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (51/20) (13/5) ∧
    SigmaActualBlockSeparable.endpointCellMass (51/20) (13/5) ≤ (434417886841/187500000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(103/40)-(1/40)) (by norm_num : ((103/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel31

namespace Hf4Quad.Panel32
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((14314652431237/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (13/5) (53/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (13/5) (53/20) ≤ (14315030850379/6000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(21/8)-(1/40)) (by norm_num : ((21/8):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel32

namespace Hf4Quad.Panel33
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((14720359204091/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (53/20) (27/10) ∧
    SigmaActualBlockSeparable.endpointCellMass (53/20) (27/10) ≤ (14720714488721/6000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(107/40)-(1/40)) (by norm_num : ((107/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel33

namespace Hf4Quad.Panel34
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((251969289693/100000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (27/10) (11/4) ∧
    SigmaActualBlockSeparable.endpointCellMass (27/10) (11/4) ≤ (2519748599913/1000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(109/40)-(1/40)) (by norm_num : ((109/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel34

namespace Hf4Quad.Panel35
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((5169376160163/2000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (11/4) (14/5) ∧
    SigmaActualBlockSeparable.endpointCellMass (11/4) (14/5) ≤ (5169480988789/2000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(111/40)-(1/40)) (by norm_num : ((111/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel35

namespace Hf4Quad.Panel36
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((5296788265951/2000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (14/5) (57/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (14/5) (57/20) ≤ (5296886951373/2000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(113/40)-(1/40)) (by norm_num : ((113/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel36

namespace Hf4Quad.Panel37
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((5421655859689/2000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (57/20) (29/10) ∧
    SigmaActualBlockSeparable.endpointCellMass (57/20) (29/10) ≤ (5421748836573/2000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(23/8)-(1/40)) (by norm_num : ((23/8):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel37

namespace Hf4Quad.Panel38
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((2772007574167/1000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (29/10) (59/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (29/10) (59/20) ≤ (554410292433/200000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(117/40)-(1/40)) (by norm_num : ((117/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel38

namespace Hf4Quad.Panel39
open Hf4Quad.CompactDag Hf4Quad.RationalModel

theorem mass_bounds : ((566390443661/200000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (59/20) 3 ∧
    SigmaActualBlockSeparable.endpointCellMass (59/20) 3 ≤ (707998417403/250000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(119/40)-(1/40)) (by norm_num : ((119/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,RationalModel.addExact,RationalModel.neg,RationalModel.scale,c380,c379,c373,c372,c288,c287,c204,c203,c115] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.Panel39
