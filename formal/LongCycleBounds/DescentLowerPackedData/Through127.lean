import LongCycleBounds.DescentLowerPackedData.N006To013
import LongCycleBounds.DescentLowerPackedData.N014To021
import LongCycleBounds.DescentLowerPackedData.N022To029
import LongCycleBounds.DescentLowerPackedData.N030To037
import LongCycleBounds.DescentLowerPackedData.N038To045
import LongCycleBounds.DescentLowerPackedData.N046To053
import LongCycleBounds.DescentLowerPackedData.N054To061
import LongCycleBounds.DescentLowerPackedData.N062To069
import LongCycleBounds.DescentLowerPackedData.N070To077
import LongCycleBounds.DescentLowerPackedData.N078To085
import LongCycleBounds.DescentLowerPackedData.N086To093
import LongCycleBounds.DescentLowerPackedData.N094To101
import LongCycleBounds.DescentLowerPackedData.N102To109
import LongCycleBounds.DescentLowerPackedData.N110To117
import LongCycleBounds.DescentLowerPackedData.N118To125
import LongCycleBounds.DescentLowerPackedData.N126To126
import LongCycleBounds.DescentLowerPackedData.N127To127
import LongCycleBounds.DescentLowerCutoffPilot

/-! Original low-cutoff signs on the same frozen meshes throughout the finite range. -/

namespace LongCycleBounds.DescentNecklace.LowerPacked

set_option maxRecDepth 32768 in
set_option maxHeartbeats 6000000 in
theorem lower_cutoff_mesh_through127 {n : ℕ} (lo : 6 ≤ n) (hi : n ≤ 127) :
    LowerCutoffMeshCertificate n := by
  interval_cases n
  · exact N006.lower_cutoff_mesh
  · exact N007.lower_cutoff_mesh
  · exact N008.lower_cutoff_mesh
  · exact N009.lower_cutoff_mesh
  · exact N010.lower_cutoff_mesh
  · exact N011.lower_cutoff_mesh
  · exact N012.lower_cutoff_mesh
  · exact N013.lower_cutoff_mesh
  · exact N014.lower_cutoff_mesh
  · exact N015.lower_cutoff_mesh
  · exact N016.lower_cutoff_mesh
  · exact N017.lower_cutoff_mesh
  · exact N018.lower_cutoff_mesh
  · exact N019.lower_cutoff_mesh
  · exact N020.lower_cutoff_mesh
  · exact N021.lower_cutoff_mesh
  · exact N022.lower_cutoff_mesh
  · exact N023.lower_cutoff_mesh
  · exact N024.lower_cutoff_mesh
  · exact N025.lower_cutoff_mesh
  · exact N026.lower_cutoff_mesh
  · exact N027.lower_cutoff_mesh
  · exact N028.lower_cutoff_mesh
  · exact N029.lower_cutoff_mesh
  · exact N030.lower_cutoff_mesh
  · exact N031.lower_cutoff_mesh
  · exact N032.lower_cutoff_mesh
  · exact N033.lower_cutoff_mesh
  · exact N034.lower_cutoff_mesh
  · exact N035.lower_cutoff_mesh
  · exact N036.lower_cutoff_mesh
  · exact N037.lower_cutoff_mesh
  · exact N038.lower_cutoff_mesh
  · exact N039.lower_cutoff_mesh
  · exact N040.lower_cutoff_mesh
  · exact N041.lower_cutoff_mesh
  · exact N042.lower_cutoff_mesh
  · exact N043.lower_cutoff_mesh
  · exact N044.lower_cutoff_mesh
  · exact N045.lower_cutoff_mesh
  · exact N046.lower_cutoff_mesh
  · exact N047.lower_cutoff_mesh
  · exact N048.lower_cutoff_mesh
  · exact N049.lower_cutoff_mesh
  · exact N050.lower_cutoff_mesh
  · exact N051.lower_cutoff_mesh
  · exact N052.lower_cutoff_mesh
  · exact N053.lower_cutoff_mesh
  · exact N054.lower_cutoff_mesh
  · exact N055.lower_cutoff_mesh
  · exact N056.lower_cutoff_mesh
  · exact N057.lower_cutoff_mesh
  · exact N058.lower_cutoff_mesh
  · exact N059.lower_cutoff_mesh
  · exact N060.lower_cutoff_mesh
  · exact N061.lower_cutoff_mesh
  · exact N062.lower_cutoff_mesh
  · exact N063.lower_cutoff_mesh
  · exact N064.lower_cutoff_mesh
  · exact N065.lower_cutoff_mesh
  · exact N066.lower_cutoff_mesh
  · exact N067.lower_cutoff_mesh
  · exact N068.lower_cutoff_mesh
  · exact N069.lower_cutoff_mesh
  · exact N070.lower_cutoff_mesh
  · exact N071.lower_cutoff_mesh
  · exact N072.lower_cutoff_mesh
  · exact N073.lower_cutoff_mesh
  · exact N074.lower_cutoff_mesh
  · exact N075.lower_cutoff_mesh
  · exact N076.lower_cutoff_mesh
  · exact N077.lower_cutoff_mesh
  · exact N078.lower_cutoff_mesh
  · exact N079.lower_cutoff_mesh
  · exact N080.lower_cutoff_mesh
  · exact N081.lower_cutoff_mesh
  · exact N082.lower_cutoff_mesh
  · exact N083.lower_cutoff_mesh
  · exact N084.lower_cutoff_mesh
  · exact N085.lower_cutoff_mesh
  · exact N086.lower_cutoff_mesh
  · exact N087.lower_cutoff_mesh
  · exact N088.lower_cutoff_mesh
  · exact N089.lower_cutoff_mesh
  · exact N090.lower_cutoff_mesh
  · exact N091.lower_cutoff_mesh
  · exact N092.lower_cutoff_mesh
  · exact N093.lower_cutoff_mesh
  · exact N094.lower_cutoff_mesh
  · exact N095.lower_cutoff_mesh
  · exact N096.lower_cutoff_mesh
  · exact N097.lower_cutoff_mesh
  · exact N098.lower_cutoff_mesh
  · exact N099.lower_cutoff_mesh
  · exact N100.lower_cutoff_mesh
  · exact N101.lower_cutoff_mesh
  · exact N102.lower_cutoff_mesh
  · exact N103.lower_cutoff_mesh
  · exact N104.lower_cutoff_mesh
  · exact N105.lower_cutoff_mesh
  · exact N106.lower_cutoff_mesh
  · exact N107.lower_cutoff_mesh
  · exact N108.lower_cutoff_mesh
  · exact N109.lower_cutoff_mesh
  · exact N110.lower_cutoff_mesh
  · exact N111.lower_cutoff_mesh
  · exact N112.lower_cutoff_mesh
  · exact N113.lower_cutoff_mesh
  · exact N114.lower_cutoff_mesh
  · exact N115.lower_cutoff_mesh
  · exact N116.lower_cutoff_mesh
  · exact N117.lower_cutoff_mesh
  · exact N118.lower_cutoff_mesh
  · exact N119.lower_cutoff_mesh
  · exact N120.lower_cutoff_mesh
  · exact N121.lower_cutoff_mesh
  · exact N122.lower_cutoff_mesh
  · exact N123.lower_cutoff_mesh
  · exact N124.lower_cutoff_mesh
  · exact N125.lower_cutoff_mesh
  · exact N126.lower_cutoff_mesh
  · exact N127.lower_cutoff_mesh

theorem lower_cutoff_mesh_three : LowerCutoffMeshCertificate 3 := Size3.lower_cutoff_mesh

#print axioms lower_cutoff_mesh_through127
#print axioms lower_cutoff_mesh_three

end LongCycleBounds.DescentNecklace.LowerPacked
