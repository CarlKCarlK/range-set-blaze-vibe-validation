import RangeSetBlaze.Basic

namespace RangeSetBlaze

open IntRange
open IntRange.NR
open scoped IntRange.NR

/-!
Algo B partitions the entire canonical range list into ranges before,
mergeable with, and after the input, then glues the middle block. Its partition
witnesses and rebuild proofs are private implementation details.
-/

section
open Classical

private structure SplitWitness (curr : NR) (xs : List NR) where
  before : List NR
  touching : List NR
  after : List NR
  order : xs = before ++ touching ++ after
  before_ok : ∀ {b}, b ∈ before → b ≺ curr
  touch_ok : ∀ {t}, t ∈ touching → NR.mergeable curr t
  after_ok : ∀ {a}, a ∈ after → curr ≺ a

mutual
  private def splitBefore (curr : NR) :
      (xs : List NR) → List.Pairwise (· ≺ ·) xs →
      SplitWitness curr xs
    | [], _ =>
        { before := []
          touching := []
          after := []
          order := by simp
          before_ok := by intro _ hb; cases hb
          touch_ok := by intro _ hb; cases hb
          after_ok := by intro _ hb; cases hb }
    | x :: xs, hcanonical =>
        let head := List.pairwise_cons.1 hcanonical
        let hcanonicalTail := head.2
        match NR.Rel3.classify x curr with
        | NR.Rel3.left hx =>
            let tail := splitBefore curr xs hcanonicalTail
            { before := x :: tail.before
              touching := tail.touching
              after := tail.after
              order := by
                -- This simultaneously rewrites `xs` via `tail.order`
                -- and reshapes the RHS with cons/append associativity.
                simp [tail.order, List.cons_append, List.append_assoc]
              before_ok := by
                intro b hb
                have hb' : b = x ∨ b ∈ tail.before := by
                  simpa using hb
                cases hb' with
                | inl hbEq =>
                    subst hbEq
                    exact hx
                | inr hbMem =>
                    exact tail.before_ok hbMem
              touch_ok := tail.touch_ok
              after_ok := tail.after_ok }
        | NR.Rel3.mergeable hx =>
            splitTouching curr x (NR.mergeable_comm.mp hx) xs hcanonical
        | NR.Rel3.right hx =>
            splitAfter curr x hx xs hcanonical

  private def splitTouching (curr : NR) (x : NR) (hx : NR.mergeable curr x) :
      (xs : List NR) → List.Pairwise (· ≺ ·) (x :: xs) →
      SplitWitness curr (x :: xs)
    | [], _ =>
        { before := []
          touching := [x]
          after := []
          order := by simp
          before_ok := by intro _ hb; cases hb
          touch_ok := by
            intro t ht
            have ht' : t = x := by simpa using ht
            simpa [ht'] using hx
          after_ok := by intro _ hb; cases hb }
    | y :: ys, hcanonical =>
        have hx_tail := (List.pairwise_cons.1 hcanonical).1
        have hcanonicalTail :
            List.Pairwise (· ≺ ·) (y :: ys) :=
          (List.pairwise_cons.1 hcanonical).2
        have xBeforeY : x ≺ y := hx_tail _ (by simp)
        match NR.Rel3.classify y curr with
        | NR.Rel3.left hy =>
            have hFalse : False :=
              hx.2 (NR.before_trans xBeforeY hy)
            False.elim hFalse
        | NR.Rel3.mergeable hy =>
            let tail := splitTouching curr y (NR.mergeable_comm.mp hy) ys hcanonicalTail
            { before := []
              touching := x :: tail.touching
              after := tail.after
              order := by
                -- Show tail.before = [] by contradiction
                have hbefore : tail.before = [] := by
                  classical
                  cases hs : tail.before with
                  | nil => rfl
                  | cons b bs =>
                      have hbmem : b ∈ tail.before := by
                        simp [hs]
                      have hb_before : b ≺ curr :=
                        tail.before_ok hbmem
                      -- Put tail.order directly into a cons-shaped equality
                      have horder_cons :
                          y :: ys =
                            b :: (bs ++ tail.touching ++ tail.after) := by
                        simpa [hs, List.cons_append, List.append_assoc] using tail.order
                      -- If head is b, then y = b
                      have hy_eq : y = b := (List.cons.inj horder_cons).1
                      -- So y is also before curr
                      have hy_before : y ≺ curr := by
                        simpa [hy_eq] using hb_before
                      -- But `y` is mergeable with `curr`, so it is not before it.
                      have : False := by
                        exact hy.1 hy_before
                      exact this.elim

                -- With tail.before = [], tail.order simplifies to the desired concatenation
                have h :
                    y :: ys = tail.touching ++ tail.after := by
                  have h' := tail.order
                  simp [tail, hbefore] at h'
                  exact h'

                -- Finish: reshape with a single cons on the left
                calc
                  x :: y :: ys = x :: (tail.touching ++ tail.after) := by
                    simp [h]
                  _ = (x :: tail.touching) ++ tail.after := by
                    simp [List.cons_append]
              before_ok := by intro _ hb; cases hb
              touch_ok := by
                intro t ht
                have ht' : t = x ∨ t ∈ tail.touching :=
                  List.mem_cons.1 ht
                cases ht' with
                | inl htEq =>
                    subst htEq
                    simpa using hx
                | inr htMem =>
                    exact tail.touch_ok htMem
              after_ok := tail.after_ok }
        | NR.Rel3.right hy =>
            let tail := splitAfter curr y hy ys hcanonicalTail
            { before := []
              touching := [x]
              after := tail.after
              order := by
                classical
                have hbefore : tail.before = [] := by
                  cases hs : tail.before with
                  | nil => rfl
                  | cons b bs =>
                      have hbmem : b ∈ tail.before := by
                        simp [hs]
                      have hb_before : b ≺ curr := tail.before_ok hbmem
                      have horder_cons :
                          y :: ys =
                            b :: (bs ++ tail.touching ++ tail.after) := by
                        simpa [hs, List.cons_append, List.append_assoc] using tail.order
                      have hy_eq : y = b := (List.cons.inj horder_cons).1
                      have hy_before : y ≺ curr := by
                        simpa [hy_eq] using hb_before
                      exact (NR.before_asymm hy hy_before).elim

                have htouch : tail.touching = [] := by
                  classical
                  cases hs : tail.touching with
                  | nil => rfl
                  | cons t ts =>
                      have htmem : t ∈ tail.touching := by
                        simp [hs]
                      have ht_touch : NR.mergeable curr t := tail.touch_ok htmem
                      have horder' :
                          y :: ys =
                            t :: (ts ++ tail.after) := by
                        simpa [hbefore, hs] using tail.order
                      have hy_eq : y = t := (List.cons.inj horder').1
                      have hy_touch : NR.mergeable curr y := by
                        simpa [hy_eq] using ht_touch
                      exact (hy_touch.1 hy).elim

                have h : y :: ys = tail.after := by
                  have h := tail.order
                  simp [hbefore, htouch] at h
                  exact h
                simp [h]
              before_ok := by intro _ hb; cases hb
              touch_ok := by
                intro t ht
                have ht' : t = x := by simpa using ht
                simpa [ht'] using hx
              after_ok := tail.after_ok }

  private def splitAfter (curr : NR) (x : NR) (hx : curr ≺ x) :
      (xs : List NR) → List.Pairwise (· ≺ ·) (x :: xs) →
      SplitWitness curr (x :: xs)
    | [], _ =>
        { before := []
          touching := []
          after := [x]
          order := by simp
          before_ok := by intro _ hb; cases hb
          touch_ok := by intro _ hb; cases hb
          after_ok := by
            intro a ha
            have ha' : a = x := by simpa using ha
            simpa [ha'] using hx }
    | y :: ys, hcanonical =>
        have hx_tail := (List.pairwise_cons.1 hcanonical).1
        have hcanonicalTail :
            List.Pairwise (· ≺ ·) (y :: ys) :=
          (List.pairwise_cons.1 hcanonical).2
        have xBeforeY : x ≺ y := hx_tail _ (by simp)
        match NR.Rel3.classify y curr with
        | NR.Rel3.right hy =>
            let tail := splitAfter curr y hy ys hcanonicalTail
            { before := []
              touching := []
              after := x :: tail.after
              order := by
                have hbefore : tail.before = [] := by
                  classical
                  cases hs : tail.before with
                  | nil => rfl
                  | cons b bs =>
                      have hbmem : b ∈ tail.before := by
                        simp [hs]
                      have hb_before : b ≺ curr := tail.before_ok hbmem
                      have horder_cons :
                          y :: ys =
                            b :: (bs ++ tail.touching ++ tail.after) := by
                        simpa [hs, List.cons_append, List.append_assoc] using tail.order
                      have hy_eq : y = b := (List.cons.inj horder_cons).1
                      have hy_before : y ≺ curr := by
                        simpa [hy_eq] using hb_before
                      exact (NR.before_asymm hy hy_before).elim

                have htouch : tail.touching = [] := by
                  classical
                  cases hs : tail.touching with
                  | nil => rfl
                  | cons t ts =>
                      have htmem : t ∈ tail.touching := by
                        simp [hs]
                      have ht_touch : NR.mergeable curr t := tail.touch_ok htmem
                      have horder' :
                          y :: ys =
                            t :: (ts ++ tail.after) := by
                        simpa [hbefore, hs] using tail.order
                      have hy_eq : y = t := (List.cons.inj horder').1
                      have hy_touch : NR.mergeable curr y := by
                        simpa [hy_eq] using ht_touch
                      exact (hy_touch.1 hy).elim

                have h :
                    y :: ys = tail.after := by
                  have h := tail.order
                  simp [tail, hbefore, htouch] at h
                  exact h
                simp [h]
              before_ok := by intro _ hb; cases hb
              touch_ok := by intro _ hb; cases hb
              after_ok := by
                intro a ha
                have ha' : a = x ∨ a ∈ tail.after := by
                  simpa using ha
                cases ha' with
                | inl haEq =>
                    subst haEq
                    simpa using hx
                | inr haMem =>
                    exact tail.after_ok haMem }
        | NR.Rel3.left hy =>
            have hcy : curr ≺ y :=
              NR.before_trans hx xBeforeY
            (NR.before_asymm hcy hy).elim
        | NR.Rel3.mergeable hy =>
            have hcy : curr ≺ y :=
              NR.before_trans hx xBeforeY
            False.elim (hy.2 hcy)
end

/-- Partition `xs` into the ranges before, touching, and after `curr`. -/
private def splitRanges (curr : NR) (xs : List NR)
    (hcanonical : List.Pairwise (· ≺ ·) xs) :
    SplitWitness curr xs :=
  splitBefore curr xs hcanonical

/-- Fold `NR.glue` across a list, starting from `curr`. -/
private def glueMany (curr : NR) (ts : List NR) : NR :=
  ts.foldl (fun acc t => NR.glue acc t) curr

private lemma glueMany_sets_mergeable
    (curr : NR) (ts : List NR)
    (htouch : ∀ t ∈ ts, NR.mergeable curr t) :
    (glueMany curr ts).val.toSet =
      curr.val.toSet ∪ rangesToSet ts := by
  induction ts generalizing curr with
  | nil =>
      simp [glueMany]
  | cons t ts ih =>
      have htouch_t : NR.mergeable curr t := htouch _ (by simp)
      have htouch_tail : ∀ u ∈ ts, NR.mergeable curr u := by
        intro u hu; exact htouch u (by simp [hu])
      have hglue :
          (NR.glue curr t).val.toSet =
            curr.val.toSet ∪ t.val.toSet :=
        NR.glue_sets curr t htouch_t
      have htouch_tail' :
          ∀ u ∈ ts, NR.mergeable (NR.glue curr t) u := by
        intro u hu
        exact NR.mergeable_glue_left (htouch_tail u hu)
      have ih' := ih (NR.glue curr t) htouch_tail'
      simp [glueMany] at ih'
      simp [glueMany, ih', hglue, rangesToSet_cons,
        Set.union_left_comm, Set.union_comm]

/-- Rebuild the list by gluing the touching block. -/
private def buildSplit (curr : NR) (before touching after : List NR) :
    List NR :=
  before ++ [glueMany curr touching] ++ after

private lemma buildSplit_sets
    (curr : NR) {xs before touching after}
    (hx : xs = before ++ touching ++ after)
    (ht : ∀ t ∈ touching, NR.mergeable curr t) :
    rangesToSet (buildSplit curr before touching after) =
      curr.val.toSet ∪
        (rangesToSet touching ∪ rangesToSet before ∪ rangesToSet after) := by
  cases hx
  simp [buildSplit, glueMany_sets_mergeable curr touching ht,
    Set.union_left_comm, Set.union_comm]

/-- Legality for Algo B rebuild:
`before ++ [glueMany curr touching] ++ after` is pairwise `(· ≺ ·)`. -/
private lemma buildSplit_pairwise
    (curr : NR) {xs} (hcanonical : List.Pairwise (· ≺ ·) xs)
    (w : SplitWitness curr xs) :
    List.Pairwise (· ≺ ·)
      (buildSplit curr w.before w.touching w.after) := by
  set g := glueMany curr w.touching with hg
  have hcanonicalFull :
      List.Pairwise (· ≺ ·) (w.before ++ w.touching ++ w.after) := by
    simpa [w.order] using hcanonical
  obtain ⟨hcanonicalBefore, hcanonicalTouchAfter, hbeforeTouchAfter⟩ :=
    List.pairwise_append.1 (by simpa [List.append_assoc] using hcanonicalFull)
  obtain ⟨_, hcanonicalAfter, htouchAfter⟩ :=
    List.pairwise_append.1 hcanonicalTouchAfter
  have h_before_glue :
      ∀ b ∈ w.before, b ≺ g := by
    intro b hb
    have hb_curr : b ≺ curr := w.before_ok hb
    have hb_touch :
        ∀ t ∈ w.touching, b ≺ t := by
      intro t ht
      exact hbeforeTouchAfter b hb t (by simp [ht])
    have hb_glue_aux :
        ∀ (acc : NR) (ts : List NR),
            (∀ t ∈ ts, b ≺ t) →
            b ≺ acc →
            b ≺ glueMany acc ts := by
      intro acc ts
      induction ts generalizing acc with
      | nil =>
          intro _ hb_acc; simpa [glueMany] using hb_acc
      | cons t ts ih =>
          intro hbefore_ts hb_acc
          have hbefore_head : b ≺ t := hbefore_ts t (by simp)
          have hb_glued : b ≺ NR.glue acc t :=
            NR.before_glue hb_acc hbefore_head
          have hbefore_tail :
              ∀ u ∈ ts, b ≺ u := by
            intro u hu
            exact hbefore_ts u (by simp [hu])
          have hb_tail :=
            ih (NR.glue acc t) hbefore_tail hb_glued
          simpa [glueMany] using hb_tail
    have hb_before_glue :=
      hb_glue_aux curr w.touching hb_touch hb_curr
    simpa [hg] using hb_before_glue
  have h_glue_after :
      ∀ a ∈ w.after, g ≺ a := by
    intro a ha
    have hcurr_after : curr ≺ a := w.after_ok ha
    have htouch_to_a :
        ∀ t ∈ w.touching, t ≺ a := by
      intro t ht
      exact htouchAfter t ht a ha
    have h_aux :
        ∀ (acc : NR) (ts : List NR),
            (∀ t ∈ ts, t ≺ a) →
            acc ≺ a →
            glueMany acc ts ≺ a := by
      intro acc ts
      induction ts generalizing acc with
      | nil =>
          intro _ hacc; simpa [glueMany] using hacc
      | cons t ts ih =>
          intro hbefore_ts hacc
          have ht_before : t ≺ a := hbefore_ts t (by simp)
          have h_glued : NR.glue acc t ≺ a :=
            NR.glue_before hacc ht_before
          have hbefore_tail :
              ∀ u ∈ ts, u ≺ a := by
            intro u hu
            exact hbefore_ts u (by simp [hu])
          have ih_result :=
            ih (NR.glue acc t) hbefore_tail h_glued
          have ih_result' := ih_result
          simp [glueMany] at ih_result'
          exact ih_result'
    have h_glue := h_aux curr w.touching htouch_to_a hcurr_after
    simpa [hg] using h_glue
  have pair_before_glue :
      List.Pairwise (· ≺ ·) (w.before ++ [g]) :=
    List.pairwise_append.mpr
      ⟨hcanonicalBefore,
      List.pairwise_singleton (R := (· ≺ ·)) _,
        by
          intro b hb y hy
          rcases List.mem_singleton.1 hy with rfl
          exact h_before_glue b hb⟩
  have pair_final :
      List.Pairwise (· ≺ ·) ((w.before ++ [g]) ++ w.after) :=
    List.pairwise_append.mpr
      ⟨pair_before_glue,
        hcanonicalAfter,
        by
          intro x hx a ha
          rcases List.mem_append.1 hx with hx | hx
          · exact hbeforeTouchAfter x hx a (by simp [ha])
          · rcases List.mem_singleton.1 hx with rfl
            exact h_glue_after a ha⟩
  simpa [buildSplit, hg, List.append_assoc] using pair_final

/-- Partition-based insertion using the split/build pipeline. -/
def internalAddB (s : RangeSetBlaze) (r : IntRange) : RangeSetBlaze :=
  if hr : r.nonempty then
    let curr : NR := ⟨r, hr⟩
    let w := splitRanges curr s.ranges s.canonical
    { ranges := buildSplit curr w.before w.touching w.after
      canonical :=
        buildSplit_pairwise curr s.canonical w }
  else
    s

/-- Algo B represents exactly the union of the old range set and the input interval. -/
theorem internalAddB_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAddB s r).toSet = s.toSet ∪ r.toSet := by
  by_cases hr : r.nonempty
  · set curr : NR := ⟨r, hr⟩
    set w := splitRanges curr s.ranges s.canonical
    have hbuild :
        rangesToSet (buildSplit curr w.before w.touching w.after) =
          curr.val.toSet ∪
            (rangesToSet w.touching ∪ rangesToSet w.before ∪ rangesToSet w.after) :=
      buildSplit_sets curr w.order (fun _ ht => w.touch_ok ht)
    have hne : ¬ r.empty := (IntRange.nonempty_iff_not_empty r).1 hr
    have htoSet : (internalAddB s r).toSet =
        curr.val.toSet ∪
          (rangesToSet w.touching ∪ rangesToSet w.before ∪ rangesToSet w.after) := by
      simp [internalAddB, hne, curr, w, toSet_eq_rangesToSet, hbuild]
    have hsplit : rangesToSet s.ranges =
        rangesToSet w.before ∪ rangesToSet w.touching ∪ rangesToSet w.after := by
      simp [w.order, rangesToSet_append, Set.union_assoc]
    rw [htoSet]
    change _ = rangesToSet s.ranges ∪ r.toSet
    rw [hsplit]
    simp only [curr]
    ac_rfl
  ·
    have hEmpty : r.empty :=
      not_not.mp ((not_congr (IntRange.nonempty_iff_not_empty r)).1 hr)
    have hEmptySet : r.toSet = (∅ : Set Int) :=
      IntRange.toSet_eq_empty_of_hi_lt_lo hEmpty
    simp [internalAddB, hEmpty, hEmptySet]


end

end RangeSetBlaze
