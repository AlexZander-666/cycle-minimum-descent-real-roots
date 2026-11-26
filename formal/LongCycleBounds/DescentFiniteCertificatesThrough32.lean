import LongCycleBounds.DescentFrozenConstants
import LongCycleBounds.DescentFiniteData.N003
import LongCycleBounds.DescentFiniteData.N004
import LongCycleBounds.DescentFiniteData.N006
import LongCycleBounds.DescentFiniteData.N007
import LongCycleBounds.DescentFiniteData.N008
import LongCycleBounds.DescentFiniteData.N009
import LongCycleBounds.DescentFiniteData.N010
import LongCycleBounds.DescentFiniteData.N011
import LongCycleBounds.DescentFiniteData.N012
import LongCycleBounds.DescentFiniteData.N013
import LongCycleBounds.DescentFiniteData.N014
import LongCycleBounds.DescentFiniteData.N015
import LongCycleBounds.DescentFiniteData.N016
import LongCycleBounds.DescentSweepData.N017
import LongCycleBounds.DescentSweepData.N018
import LongCycleBounds.DescentSweepData.N019
import LongCycleBounds.DescentSweepData.N020
import LongCycleBounds.DescentSweepData.N021
import LongCycleBounds.DescentSweepData.N022
import LongCycleBounds.DescentSweepData.N023
import LongCycleBounds.DescentSweepData.N024
import LongCycleBounds.DescentSweepData.N025
import LongCycleBounds.DescentSweepData.N026
import LongCycleBounds.DescentSweepData.N027
import LongCycleBounds.DescentSweepData.N028
import LongCycleBounds.DescentSweepChunkData.N029
import LongCycleBounds.DescentSweepChunkData.N030
import LongCycleBounds.DescentSweepChunkData.N031
import LongCycleBounds.DescentSweepChunkData.N032

/-! The same checked dyadic mesh for each earlier frozen size. -/

namespace LongCycleBounds.DescentNecklace.FrozenCertificates

theorem N003.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 3 - 2 ∧ RepresentativeChecks 3 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentFiniteData.N003
    LongCycleBounds.DescentNecklace.N003.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentFiniteData.N003
    LongCycleBounds.DescentNecklace.N003.rows
  let checks := descentFrozenConst LongCycleBounds.DescentFiniteData.N003
    LongCycleBounds.DescentNecklace.N003.checks
  exact ⟨nodes, rows, by decide, checks⟩

theorem N004.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 4 - 2 ∧ RepresentativeChecks 4 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentFiniteData.N004
    LongCycleBounds.DescentNecklace.N004.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentFiniteData.N004
    LongCycleBounds.DescentNecklace.N004.rows
  let checks := descentFrozenConst LongCycleBounds.DescentFiniteData.N004
    LongCycleBounds.DescentNecklace.N004.checks
  exact ⟨nodes, rows, by decide, checks⟩

theorem N006.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 6 - 2 ∧ RepresentativeChecks 6 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentFiniteData.N006
    LongCycleBounds.DescentNecklace.N006.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentFiniteData.N006
    LongCycleBounds.DescentNecklace.N006.rows
  let checks := descentFrozenConst LongCycleBounds.DescentFiniteData.N006
    LongCycleBounds.DescentNecklace.N006.checks
  exact ⟨nodes, rows, by decide, checks⟩

theorem N007.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 7 - 2 ∧ RepresentativeChecks 7 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentFiniteData.N007
    LongCycleBounds.DescentNecklace.N007.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentFiniteData.N007
    LongCycleBounds.DescentNecklace.N007.rows
  let checks := descentFrozenConst LongCycleBounds.DescentFiniteData.N007
    LongCycleBounds.DescentNecklace.N007.checks
  exact ⟨nodes, rows, by decide, checks⟩

theorem N008.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 8 - 2 ∧ RepresentativeChecks 8 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentFiniteData.N008
    LongCycleBounds.DescentNecklace.N008.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentFiniteData.N008
    LongCycleBounds.DescentNecklace.N008.rows
  let checks := descentFrozenConst LongCycleBounds.DescentFiniteData.N008
    LongCycleBounds.DescentNecklace.N008.checks
  exact ⟨nodes, rows, by decide, checks⟩

theorem N009.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 9 - 2 ∧ RepresentativeChecks 9 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentFiniteData.N009
    LongCycleBounds.DescentNecklace.N009.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentFiniteData.N009
    LongCycleBounds.DescentNecklace.N009.rows
  let checks := descentFrozenConst LongCycleBounds.DescentFiniteData.N009
    LongCycleBounds.DescentNecklace.N009.checks
  exact ⟨nodes, rows, by decide, checks⟩

theorem N010.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 10 - 2 ∧ RepresentativeChecks 10 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentFiniteData.N010
    LongCycleBounds.DescentNecklace.N010.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentFiniteData.N010
    LongCycleBounds.DescentNecklace.N010.rows
  let checks := descentFrozenConst LongCycleBounds.DescentFiniteData.N010
    LongCycleBounds.DescentNecklace.N010.checks
  exact ⟨nodes, rows, by decide, checks⟩

theorem N011.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 11 - 2 ∧ RepresentativeChecks 11 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentFiniteData.N011
    LongCycleBounds.DescentNecklace.N011.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentFiniteData.N011
    LongCycleBounds.DescentNecklace.N011.rows
  let checks := descentFrozenConst LongCycleBounds.DescentFiniteData.N011
    LongCycleBounds.DescentNecklace.N011.checks
  exact ⟨nodes, rows, by decide, checks⟩

theorem N012.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 12 - 2 ∧ RepresentativeChecks 12 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentFiniteData.N012
    LongCycleBounds.DescentNecklace.N012.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentFiniteData.N012
    LongCycleBounds.DescentNecklace.N012.rows
  let checks := descentFrozenConst LongCycleBounds.DescentFiniteData.N012
    LongCycleBounds.DescentNecklace.N012.checks
  exact ⟨nodes, rows, by decide, checks⟩

theorem N013.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 13 - 2 ∧ RepresentativeChecks 13 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentFiniteData.N013
    LongCycleBounds.DescentNecklace.N013.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentFiniteData.N013
    LongCycleBounds.DescentNecklace.N013.rows
  let checks := descentFrozenConst LongCycleBounds.DescentFiniteData.N013
    LongCycleBounds.DescentNecklace.N013.checks
  exact ⟨nodes, rows, by decide, checks⟩

theorem N014.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 14 - 2 ∧ RepresentativeChecks 14 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentFiniteData.N014
    LongCycleBounds.DescentNecklace.N014.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentFiniteData.N014
    LongCycleBounds.DescentNecklace.N014.rows
  let checks := descentFrozenConst LongCycleBounds.DescentFiniteData.N014
    LongCycleBounds.DescentNecklace.N014.checks
  exact ⟨nodes, rows, by decide, checks⟩

theorem N015.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 15 - 2 ∧ RepresentativeChecks 15 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentFiniteData.N015
    LongCycleBounds.DescentNecklace.N015.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentFiniteData.N015
    LongCycleBounds.DescentNecklace.N015.rows
  let checks := descentFrozenConst LongCycleBounds.DescentFiniteData.N015
    LongCycleBounds.DescentNecklace.N015.checks
  exact ⟨nodes, rows, by decide, checks⟩

theorem N016.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 16 - 2 ∧ RepresentativeChecks 16 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentFiniteData.N016
    LongCycleBounds.DescentNecklace.N016.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentFiniteData.N016
    LongCycleBounds.DescentNecklace.N016.rows
  let checks := descentFrozenConst LongCycleBounds.DescentFiniteData.N016
    LongCycleBounds.DescentNecklace.N016.checks
  exact ⟨nodes, rows, by decide, checks⟩

theorem N017.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 17 - 2 ∧ RepresentativeChecks 17 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentSweepData.N017
    LongCycleBounds.DescentNecklace.Sweep.N017.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentSweepData.N017
    LongCycleBounds.DescentNecklace.Sweep.N017.rows
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N017
    LongCycleBounds.DescentNecklace.Sweep.N017.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N017
    LongCycleBounds.DescentNecklace.Sweep.N017.signs
  exact ⟨nodes, rows, by decide, representativeChecks_of_shared (n := 17) (by decide) nodes rows counts signs⟩

theorem N018.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 18 - 2 ∧ RepresentativeChecks 18 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentSweepData.N018
    LongCycleBounds.DescentNecklace.Sweep.N018.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentSweepData.N018
    LongCycleBounds.DescentNecklace.Sweep.N018.rows
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N018
    LongCycleBounds.DescentNecklace.Sweep.N018.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N018
    LongCycleBounds.DescentNecklace.Sweep.N018.signs
  exact ⟨nodes, rows, by decide, representativeChecks_of_shared (n := 18) (by decide) nodes rows counts signs⟩

theorem N019.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 19 - 2 ∧ RepresentativeChecks 19 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentSweepData.N019
    LongCycleBounds.DescentNecklace.Sweep.N019.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentSweepData.N019
    LongCycleBounds.DescentNecklace.Sweep.N019.rows
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N019
    LongCycleBounds.DescentNecklace.Sweep.N019.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N019
    LongCycleBounds.DescentNecklace.Sweep.N019.signs
  exact ⟨nodes, rows, by decide, representativeChecks_of_shared (n := 19) (by decide) nodes rows counts signs⟩

theorem N020.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 20 - 2 ∧ RepresentativeChecks 20 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentSweepData.N020
    LongCycleBounds.DescentNecklace.Sweep.N020.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentSweepData.N020
    LongCycleBounds.DescentNecklace.Sweep.N020.rows
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N020
    LongCycleBounds.DescentNecklace.Sweep.N020.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N020
    LongCycleBounds.DescentNecklace.Sweep.N020.signs
  exact ⟨nodes, rows, by decide, representativeChecks_of_shared (n := 20) (by decide) nodes rows counts signs⟩

theorem N021.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 21 - 2 ∧ RepresentativeChecks 21 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentSweepData.N021
    LongCycleBounds.DescentNecklace.Sweep.N021.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentSweepData.N021
    LongCycleBounds.DescentNecklace.Sweep.N021.rows
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N021
    LongCycleBounds.DescentNecklace.Sweep.N021.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N021
    LongCycleBounds.DescentNecklace.Sweep.N021.signs
  exact ⟨nodes, rows, by decide, representativeChecks_of_shared (n := 21) (by decide) nodes rows counts signs⟩

theorem N022.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 22 - 2 ∧ RepresentativeChecks 22 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentSweepData.N022
    LongCycleBounds.DescentNecklace.Sweep.N022.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentSweepData.N022
    LongCycleBounds.DescentNecklace.Sweep.N022.rows
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N022
    LongCycleBounds.DescentNecklace.Sweep.N022.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N022
    LongCycleBounds.DescentNecklace.Sweep.N022.signs
  exact ⟨nodes, rows, by decide, representativeChecks_of_shared (n := 22) (by decide) nodes rows counts signs⟩

theorem N023.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 23 - 2 ∧ RepresentativeChecks 23 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentSweepData.N023
    LongCycleBounds.DescentNecklace.Sweep.N023.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentSweepData.N023
    LongCycleBounds.DescentNecklace.Sweep.N023.rows
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N023
    LongCycleBounds.DescentNecklace.Sweep.N023.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N023
    LongCycleBounds.DescentNecklace.Sweep.N023.signs
  exact ⟨nodes, rows, by decide, representativeChecks_of_shared (n := 23) (by decide) nodes rows counts signs⟩

theorem N024.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 24 - 2 ∧ RepresentativeChecks 24 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentSweepData.N024
    LongCycleBounds.DescentNecklace.Sweep.N024.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentSweepData.N024
    LongCycleBounds.DescentNecklace.Sweep.N024.rows
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N024
    LongCycleBounds.DescentNecklace.Sweep.N024.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N024
    LongCycleBounds.DescentNecklace.Sweep.N024.signs
  exact ⟨nodes, rows, by decide, representativeChecks_of_shared (n := 24) (by decide) nodes rows counts signs⟩

theorem N025.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 25 - 2 ∧ RepresentativeChecks 25 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentSweepData.N025
    LongCycleBounds.DescentNecklace.Sweep.N025.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentSweepData.N025
    LongCycleBounds.DescentNecklace.Sweep.N025.rows
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N025
    LongCycleBounds.DescentNecklace.Sweep.N025.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N025
    LongCycleBounds.DescentNecklace.Sweep.N025.signs
  exact ⟨nodes, rows, by decide, representativeChecks_of_shared (n := 25) (by decide) nodes rows counts signs⟩

theorem N026.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 26 - 2 ∧ RepresentativeChecks 26 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentSweepData.N026
    LongCycleBounds.DescentNecklace.Sweep.N026.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentSweepData.N026
    LongCycleBounds.DescentNecklace.Sweep.N026.rows
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N026
    LongCycleBounds.DescentNecklace.Sweep.N026.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N026
    LongCycleBounds.DescentNecklace.Sweep.N026.signs
  exact ⟨nodes, rows, by decide, representativeChecks_of_shared (n := 26) (by decide) nodes rows counts signs⟩

theorem N027.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 27 - 2 ∧ RepresentativeChecks 27 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentSweepData.N027
    LongCycleBounds.DescentNecklace.Sweep.N027.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentSweepData.N027
    LongCycleBounds.DescentNecklace.Sweep.N027.rows
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N027
    LongCycleBounds.DescentNecklace.Sweep.N027.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N027
    LongCycleBounds.DescentNecklace.Sweep.N027.signs
  exact ⟨nodes, rows, by decide, representativeChecks_of_shared (n := 27) (by decide) nodes rows counts signs⟩

theorem N028.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 28 - 2 ∧ RepresentativeChecks 28 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentSweepData.N028
    LongCycleBounds.DescentNecklace.Sweep.N028.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentSweepData.N028
    LongCycleBounds.DescentNecklace.Sweep.N028.rows
  let counts := descentFrozenConst LongCycleBounds.DescentSweepData.N028
    LongCycleBounds.DescentNecklace.Sweep.N028.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepData.N028
    LongCycleBounds.DescentNecklace.Sweep.N028.signs
  exact ⟨nodes, rows, by decide, representativeChecks_of_shared (n := 28) (by decide) nodes rows counts signs⟩

theorem N029.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 29 - 2 ∧ RepresentativeChecks 29 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N029
    LongCycleBounds.DescentNecklace.SweepChunks.N029.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N029
    LongCycleBounds.DescentNecklace.SweepChunks.N029.rows
  let atAlphabet := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N029
    LongCycleBounds.DescentNecklace.SweepChunks.N029.atAlphabet
  let swept := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N029
    LongCycleBounds.DescentNecklace.SweepChunks.N029.swept
  let counts := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N029
    LongCycleBounds.DescentNecklace.SweepChunks.N029.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N029
    LongCycleBounds.DescentNecklace.SweepChunks.N029.signs
  exact ⟨nodes, rows, by decide, representativeChecks_of_sweepChunks (n := 29) (by decide) nodes rows
    atAlphabet swept counts signs⟩

theorem N030.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 30 - 2 ∧ RepresentativeChecks 30 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N030
    LongCycleBounds.DescentNecklace.SweepChunks.N030.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N030
    LongCycleBounds.DescentNecklace.SweepChunks.N030.rows
  let atAlphabet := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N030
    LongCycleBounds.DescentNecklace.SweepChunks.N030.atAlphabet
  let swept := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N030
    LongCycleBounds.DescentNecklace.SweepChunks.N030.swept
  let counts := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N030
    LongCycleBounds.DescentNecklace.SweepChunks.N030.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N030
    LongCycleBounds.DescentNecklace.SweepChunks.N030.signs
  exact ⟨nodes, rows, by decide, representativeChecks_of_sweepChunks (n := 30) (by decide) nodes rows
    atAlphabet swept counts signs⟩

theorem N031.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 31 - 2 ∧ RepresentativeChecks 31 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N031
    LongCycleBounds.DescentNecklace.SweepChunks.N031.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N031
    LongCycleBounds.DescentNecklace.SweepChunks.N031.rows
  let atAlphabet := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N031
    LongCycleBounds.DescentNecklace.SweepChunks.N031.atAlphabet
  let swept := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N031
    LongCycleBounds.DescentNecklace.SweepChunks.N031.swept
  let counts := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N031
    LongCycleBounds.DescentNecklace.SweepChunks.N031.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N031
    LongCycleBounds.DescentNecklace.SweepChunks.N031.signs
  exact ⟨nodes, rows, by decide, representativeChecks_of_sweepChunks (n := 31) (by decide) nodes rows
    atAlphabet swept counts signs⟩

theorem N032.finite_certificate :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = 32 - 2 ∧ RepresentativeChecks 32 nodes rows := by
  let nodes := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N032
    LongCycleBounds.DescentNecklace.SweepChunks.N032.nodes
  let rows := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N032
    LongCycleBounds.DescentNecklace.SweepChunks.N032.rows
  let atAlphabet := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N032
    LongCycleBounds.DescentNecklace.SweepChunks.N032.atAlphabet
  let swept := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N032
    LongCycleBounds.DescentNecklace.SweepChunks.N032.swept
  let counts := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N032
    LongCycleBounds.DescentNecklace.SweepChunks.N032.counts
  let signs := descentFrozenConst LongCycleBounds.DescentSweepChunkData.N032
    LongCycleBounds.DescentNecklace.SweepChunks.N032.signs
  exact ⟨nodes, rows, by decide, representativeChecks_of_sweepChunks (n := 32) (by decide) nodes rows
    atAlphabet swept counts signs⟩

/-- Every frozen nonexceptional size has representative rows with one common checked mesh. -/
theorem finite_certificate_through32 {n : ℕ} (lo : 3 ≤ n) (hi : n ≤ 32) (five : n ≠ 5) :
    ∃ nodes : Array LongCycleFinite.Dyadic, ∃ rows : Array (List ℤ),
      nodes.size = n - 2 ∧ RepresentativeChecks n nodes rows := by
  interval_cases n
  · exact N003.finite_certificate
  · exact N004.finite_certificate
  · exact (five rfl).elim
  · exact N006.finite_certificate
  · exact N007.finite_certificate
  · exact N008.finite_certificate
  · exact N009.finite_certificate
  · exact N010.finite_certificate
  · exact N011.finite_certificate
  · exact N012.finite_certificate
  · exact N013.finite_certificate
  · exact N014.finite_certificate
  · exact N015.finite_certificate
  · exact N016.finite_certificate
  · exact N017.finite_certificate
  · exact N018.finite_certificate
  · exact N019.finite_certificate
  · exact N020.finite_certificate
  · exact N021.finite_certificate
  · exact N022.finite_certificate
  · exact N023.finite_certificate
  · exact N024.finite_certificate
  · exact N025.finite_certificate
  · exact N026.finite_certificate
  · exact N027.finite_certificate
  · exact N028.finite_certificate
  · exact N029.finite_certificate
  · exact N030.finite_certificate
  · exact N031.finite_certificate
  · exact N032.finite_certificate

#print axioms finite_certificate_through32

end LongCycleBounds.DescentNecklace.FrozenCertificates
