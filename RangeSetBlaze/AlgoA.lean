import RangeSetBlaze.Basic

namespace RangeSetBlaze

open IntRange
open IntRange.NR
open scoped IntRange.NR

/-!
Algo A is the original recursive insertion model. Its raw list operation and
proof projections are private; the module exposes only the algorithm and its
set-level correctness theorem.
-/

private def insert
  (curr : IntRange.NR)
  : (xs : List IntRange.NR) → List.Pairwise (· ≺ ·) xs →
      { ys : List IntRange.NR //
        List.Pairwise (· ≺ ·) ys ∧
        rangesToSet ys = curr.val.toSet ∪ rangesToSet xs ∧
        ∀ {z : IntRange.NR},
          (∀ y ∈ xs, z ≺ y) → z ≺ curr →
          ∀ y ∈ ys, z ≺ y }
  | [], _ =>
      ⟨[curr], by
          exact List.pairwise_singleton (R := (· ≺ ·)) (a := curr),
        by simp [rangesToSet],
        by
          intro z _ hzc y hy
          have hy' : y = curr := List.mem_singleton.mp hy
          simpa [hy'] using hzc⟩
  | x :: xs, hpx =>
      have hx_tail : ∀ y ∈ xs, x ≺ y := (List.pairwise_cons.1 hpx).1
      have h_tail : List.Pairwise (· ≺ ·) xs := (List.pairwise_cons.1 hpx).2
      match IntRange.NR.Rel3.classify curr x with
      | IntRange.NR.Rel3.left hcx =>
          let hcurr_tail : ∀ y ∈ xs, curr ≺ y :=
            by
              intro y hy
              exact NR.before_trans hcx (hx_tail y hy)
          let pair : List.Pairwise (· ≺ ·) (curr :: x :: xs) :=
            List.pairwise_cons.2
              ⟨by
                  intro y hy
                  rcases List.mem_cons.1 hy with hy | hy
                  · simpa [hy] using hcx
                  · exact hcurr_tail y hy,
                hpx⟩
          let mono :
              ∀ {z : IntRange.NR},
                (∀ y ∈ x :: xs, z ≺ y) → z ≺ curr →
                ∀ y ∈ curr :: x :: xs, z ≺ y :=
            by
              intro z hzxs hzc y hy
              rcases List.mem_cons.1 hy with hy | hy
              · simpa [hy] using hzc
              · exact hzxs y hy
          ⟨curr :: x :: xs, pair, by simp [rangesToSet_cons], mono⟩
      | IntRange.NR.Rel3.right hxc =>
          let ⟨ys, hpair, hset, hmon⟩ := insert curr xs h_tail
          let hx_all : ∀ y ∈ ys, x ≺ y :=
            hmon
              (by
                intro y hy
                exact hx_tail y hy)
              hxc
          let pair : List.Pairwise (· ≺ ·) (x :: ys) :=
            List.pairwise_cons.2 ⟨hx_all, hpair⟩
          let setEq :
              rangesToSet (x :: ys) = curr.val.toSet ∪ rangesToSet (x :: xs) :=
            by
              have := congrArg (fun s => x.val.toSet ∪ s) hset
              simpa [rangesToSet_cons, Set.union_left_comm, Set.union_assoc, Set.union_comm] using this
          let mono :
              ∀ {z : IntRange.NR},
                (∀ y ∈ x :: xs, z ≺ y) → z ≺ curr →
                ∀ y ∈ x :: ys, z ≺ y :=
            by
              intro z hzxs hzc y hy
              rcases List.mem_cons.1 hy with hy | hy
              · simpa [hy] using hzxs x (by simp)
              · have hz_tail : ∀ w ∈ xs, z ≺ w := by
                  intro w hw
                  exact hzxs w (List.mem_cons_of_mem _ hw)
                exact hmon hz_tail hzc y hy
          ⟨x :: ys, pair, setEq, mono⟩
      | IntRange.NR.Rel3.mergeable hmergeable =>
          let glued := IntRange.NR.glue curr x
          have gl_sets : glued.val.toSet = curr.val.toSet ∪ x.val.toSet :=
            IntRange.NR.glue_sets curr x hmergeable
          let ⟨ys, hpair, hset, hmon⟩ := insert glued xs h_tail
          let setEq :
              rangesToSet ys = curr.val.toSet ∪ rangesToSet (x :: xs) :=
            by
              simpa [rangesToSet_cons, gl_sets, Set.union_assoc,
                Set.union_left_comm, Set.union_comm] using hset
          let mono :
              ∀ {z : IntRange.NR},
                (∀ y ∈ x :: xs, z ≺ y) → z ≺ curr →
                ∀ y ∈ ys, z ≺ y :=
            by
              intro z hzxs hzc y hy
              have hz_tail : ∀ w ∈ xs, z ≺ w := by
                intro w hw
                exact hzxs w (List.mem_cons_of_mem _ hw)
              have hzx : z ≺ x := hzxs x (by simp)
              have hzg : z ≺ glued := NR.before_glue hzc hzx
              exact hmon hz_tail hzg y hy
          ⟨ys, hpair, setEq, mono⟩

open Classical

/-- Add a (possibly empty) range to a `RangeSetBlaze`. -/
def internalAddA (s : RangeSetBlaze) (r : IntRange) : RangeSetBlaze :=
  if hr : r.nonempty then
    let curr : IntRange.NR := ⟨r, hr⟩
    let ⟨ys, hpair, _, _⟩ := insert curr s.ranges s.canonical
    ⟨ys, hpair⟩
  else s

/-- Algo A represents exactly the union of the old range set and the input interval. -/
theorem internalAddA_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAddA s r).toSet = s.toSet ∪ r.toSet := by
  classical
  by_cases hr : r.nonempty
  · have hnotEmpty := (IntRange.nonempty_iff_not_empty r).mp hr
    generalize hresult : insert ⟨r, hr⟩ s.ranges s.canonical = result
    rcases result with ⟨ys, hpair, hset, _⟩
    simpa [internalAddA, hnotEmpty, hresult, toSet, Set.union_comm] using hset
  · have hempty : r.toSet = (∅ : Set Int) := by
      rw [IntRange.toSet_eq_empty_iff]
      simpa [IntRange.nonempty, not_le] using hr
    have hisEmpty := (IntRange.nonempty_iff_not_empty r).not.mp hr
    simp [internalAddA, hisEmpty, hempty]

end RangeSetBlaze
