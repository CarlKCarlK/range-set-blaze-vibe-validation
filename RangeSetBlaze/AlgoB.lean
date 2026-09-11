import RangeSetBlaze.Basic

namespace RangeSetBlaze

open IntRange
open IntRange.NR
open scoped IntRange.NR

section
open Classical

/-- Strictly before the current range (with a gap). -/
def isBefore (curr : NR) (x : NR) : Prop :=
  x ≺ curr

/-- Strictly after the current range (with a gap). -/
def isAfter (curr : NR) (x : NR) : Prop :=
  curr ≺ x

instance (curr : NR) : DecidablePred (isBefore curr) :=
  fun x => inferInstanceAs (Decidable (x ≺ curr))

instance (curr : NR) : DecidablePred (isAfter curr) :=
  fun x => inferInstanceAs (Decidable (curr ≺ x))

structure SplitWitness (curr : NR) (xs : List NR) where
  before : List NR
  touching : List NR
  after : List NR
  order : xs = before ++ touching ++ after
  before_ok : ∀ {b}, b ∈ before → isBefore curr b
  touch_ok : ∀ {t}, t ∈ touching → NR.mergeable curr t
  after_ok : ∀ {a}, a ∈ after → isAfter curr a

mutual
  def splitBefore (curr : NR) :
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
    | x :: xs, ok =>
        let head := List.pairwise_cons.1 ok
        let okTail := head.2
        match NR.Rel3.classify x curr with
        | NR.Rel3.left hx =>
            let tail := splitBefore curr xs okTail
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
            splitTouching curr x (NR.mergeable_comm.mp hx) xs ok
        | NR.Rel3.right hx =>
            splitAfter curr x hx xs ok

  def splitTouching (curr : NR) (x : NR) (hx : NR.mergeable curr x) :
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
    | y :: ys, ok =>
        have hx_tail := (List.pairwise_cons.1 ok).1
        have okTail :
            List.Pairwise (· ≺ ·) (y :: ys) :=
          (List.pairwise_cons.1 ok).2
        have xBeforeY : x ≺ y := hx_tail _ (by simp)
        match NR.Rel3.classify y curr with
        | NR.Rel3.left hy =>
            have hFalse : False :=
              hx.2 (before_trans xBeforeY hy)
            False.elim hFalse
        | NR.Rel3.mergeable hy =>
            let tail := splitTouching curr y (NR.mergeable_comm.mp hy) ys okTail
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
                      have hb_before : isBefore curr b :=
                        tail.before_ok hbmem
                      -- Put tail.order directly into a cons-shaped equality
                      have horder_cons :
                          y :: ys =
                            b :: (bs ++ tail.touching ++ tail.after) := by
                        simpa [hs, List.cons_append, List.append_assoc] using tail.order
                      -- If head is b, then y = b
                      have hy_eq : y = b := (List.cons.inj horder_cons).1
                      -- So y is also before curr
                      have hy_before : isBefore curr y := by
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
            let tail := splitAfter curr y hy ys okTail
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
                      have hb_before : isBefore curr b := tail.before_ok hbmem
                      have horder_cons :
                          y :: ys =
                            b :: (bs ++ tail.touching ++ tail.after) := by
                        simpa [hs, List.cons_append, List.append_assoc] using tail.order
                      have hy_eq : y = b := (List.cons.inj horder_cons).1
                      have hy_before : isBefore curr y := by
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

  def splitAfter (curr : NR) (x : NR) (hx : isAfter curr x) :
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
    | y :: ys, ok =>
        have hx_tail := (List.pairwise_cons.1 ok).1
        have okTail :
            List.Pairwise (· ≺ ·) (y :: ys) :=
          (List.pairwise_cons.1 ok).2
        have xBeforeY : x ≺ y := hx_tail _ (by simp)
        match NR.Rel3.classify y curr with
        | NR.Rel3.right hy =>
            let tail := splitAfter curr y hy ys okTail
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
                      have hb_before : isBefore curr b := tail.before_ok hbmem
                      have horder_cons :
                          y :: ys =
                            b :: (bs ++ tail.touching ++ tail.after) := by
                        simpa [hs, List.cons_append, List.append_assoc] using tail.order
                      have hy_eq : y = b := (List.cons.inj horder_cons).1
                      have hy_before : isBefore curr y := by
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
              before_trans hx xBeforeY
            (NR.before_asymm hcy hy).elim
        | NR.Rel3.mergeable hy =>
            have hcy : curr ≺ y :=
              before_trans hx xBeforeY
            False.elim (hy.2 hcy)
end

/-- Once we are in the touching phase, the recursive tail cannot place any
element in the `before` block. -/
theorem splitTouching_tail_before_nil
    (curr y : NR) (hy : NR.mergeable curr y)
    (ys : List NR) (ok : List.Pairwise (· ≺ ·) (y :: ys)) :
    (splitTouching curr y hy ys ok).before = [] := by
  revert y hy ok
  induction ys with
  | nil =>
      intro y hy _; rfl
  | cons z zs ih =>
      intro y hy ok
      rcases List.pairwise_cons.1 ok with ⟨hx_tail, okTail⟩
      have hyz : y ≺ z := hx_tail _ (by simp)
      cases hcls : NR.Rel3.classify z curr with
      | left hz =>
          exact (hy.2 (before_trans hyz hz)).elim
      | mergeable hz =>
          simp [splitTouching, hcls]
      | right hz =>
          simp [splitTouching, hcls]

/-- Once we are in the after phase, the recursive tail cannot place any element
in the `touching` block. -/
theorem splitAfter_tail_touching_nil
    (curr y : NR) (hy : isAfter curr y)
    (ys : List NR) (ok : List.Pairwise (· ≺ ·) (y :: ys)) :
    (splitAfter curr y hy ys ok).touching = [] := by
  revert y hy ok
  induction ys with
  | nil =>
      intro y hy _; rfl
  | cons z zs ih =>
      intro y hy ok
      rcases List.pairwise_cons.1 ok with ⟨hx_tail, okTail⟩
      have hyz : y ≺ z := hx_tail _ (by simp)
      cases hcls : NR.Rel3.classify z curr with
      | right hz =>
          simp [splitAfter, hcls]
      | left hz =>
          have hcy : curr ≺ z := before_trans hy hyz
          exact (NR.before_asymm hcy hz).elim
      | mergeable hz =>
          have hcy : curr ≺ z := before_trans hy hyz
          exact (hz.2 hcy).elim

/-- Once we are in the after phase, the recursive tail cannot place any element
in the `before` block. -/
theorem splitAfter_tail_before_nil
    (curr y : NR) (hy : isAfter curr y)
    (ys : List NR) (ok : List.Pairwise (· ≺ ·) (y :: ys)) :
    (splitAfter curr y hy ys ok).before = [] := by
  revert y hy ok
  induction ys with
  | nil =>
      intro y hy _; rfl
  | cons z zs ih =>
      intro y hy ok
      rcases List.pairwise_cons.1 ok with ⟨hx_tail, okTail⟩
      have hyz : y ≺ z := hx_tail _ (by simp)
      cases hcls : NR.Rel3.classify z curr with
      | right hz =>
          simp [splitAfter, hcls]
      | left hz =>
          have hcy : curr ≺ z := before_trans hy hyz
          exact (NR.before_asymm hcy hz).elim
      | mergeable hz =>
          have hcy : curr ≺ z := before_trans hy hyz
          exact (hz.2 hcy).elim

/-- Partition `xs` into the ranges before, touching, and after `curr`. -/
def splitRanges (curr : NR) (xs : List NR)
    (ok : List.Pairwise (· ≺ ·) xs) :
    SplitWitness curr xs :=
  splitBefore curr xs ok

/-- Fold `NR.glue` across a list, starting from `curr`. -/
def glueMany (curr : NR) (ts : List NR) : NR :=
  ts.foldl (fun acc t => NR.glue acc t) curr

lemma mergeable_after_glue_step
    (curr x y : NR)
    (hx : NR.mergeable curr x)
    (hy : NR.mergeable curr y) :
    NR.mergeable (NR.glue curr x) y := by
  rcases hx with ⟨hx₁, hx₂⟩
  rcases hy with ⟨hy₁, hy₂⟩
  constructor
  · intro h
    unfold NR.glue IntRange.mergeRange NR.before at h
    have hmax :
        curr.val.hi + 1 ≤ (max curr.val.hi x.val.hi) + 1 := by
      have h := add_le_add_right (le_max_left curr.val.hi x.val.hi) (1 : Int)
      simpa using h
    have : curr.val.hi + 1 < y.val.lo := lt_of_le_of_lt hmax h
    exact hy₁ this
  · intro h
    unfold NR.glue IntRange.mergeRange NR.before at h
    have : y.val.hi + 1 < curr.val.lo :=
      lt_of_lt_of_le h (min_le_left _ _)
    exact hy₂ this

lemma glueMany_sets_mergeable
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
        exact mergeable_after_glue_step curr t u htouch_t (htouch_tail u hu)
      have ih' := ih (NR.glue curr t) htouch_tail'
      simp [glueMany] at ih'
      simp [glueMany, ih', hglue, rangesToSet_cons,
        Set.union_left_comm, Set.union_comm]

/-- Rebuild the list by gluing the touching block. -/
def buildSplit (curr : NR) (before touching after : List NR) :
    List NR :=
  before ++ [glueMany curr touching] ++ after

lemma buildSplit_sets
    (curr : NR) {xs before touching after}
    (hx : xs = before ++ touching ++ after)
    (ht : ∀ t ∈ touching, NR.mergeable curr t) :
    rangesToSet (buildSplit curr before touching after) =
      curr.val.toSet ∪
        (rangesToSet touching ∪ rangesToSet before ∪ rangesToSet after) := by
  cases hx
  simp [buildSplit, glueMany_sets_mergeable curr touching ht,
    Set.union_left_comm, Set.union_comm]

/-- Everything in `before` is before everything in `touching`. -/
lemma split_before_before_touch
    (curr : NR) {xs} (ok : List.Pairwise (· ≺ ·) xs)
    (w : SplitWitness curr xs) :
    ∀ ⦃b⦄, b ∈ w.before → ∀ ⦃t⦄, t ∈ w.touching → b ≺ t := by
  have ok' :
      List.Pairwise (· ≺ ·) (w.before ++ w.touching ++ w.after) := by
    simpa [w.order] using ok
  have ok'' :
      List.Pairwise (· ≺ ·)
        (w.before ++ (w.touching ++ w.after)) := by
    simpa [List.append_assoc] using ok'
  obtain ⟨_, ok_tail, cross_before⟩ :=
    List.pairwise_append.1 ok''
  intro b hb t ht
  have ht' : t ∈ w.touching ++ w.after := by
    simp [List.mem_append, ht]
  exact cross_before (a := b) (b := t) hb ht'

/-- Everything in `before` is before everything in `after`. -/
lemma split_before_before_after
    (curr : NR) {xs} (ok : List.Pairwise (· ≺ ·) xs)
    (w : SplitWitness curr xs) :
    ∀ ⦃b⦄, b ∈ w.before → ∀ ⦃a⦄, a ∈ w.after → b ≺ a := by
  have ok' :
      List.Pairwise (· ≺ ·) (w.before ++ w.touching ++ w.after) := by
    simpa [w.order] using ok
  have ok'' :
      List.Pairwise (· ≺ ·)
        (w.before ++ (w.touching ++ w.after)) := by
    simpa [List.append_assoc] using ok'
  obtain ⟨_, ok_tail, cross_before⟩ :=
    List.pairwise_append.1 ok''
  intro b hb a ha
  have ha' : a ∈ w.touching ++ w.after := by
    simp [List.mem_append, ha]
  exact cross_before (a := b) (b := a) hb ha'

/-- Everything in `touching` is before everything in `after`. -/
lemma split_touch_before_after
    (curr : NR) {xs} (ok : List.Pairwise (· ≺ ·) xs)
    (w : SplitWitness curr xs) :
    ∀ ⦃t⦄, t ∈ w.touching → ∀ ⦃a⦄, a ∈ w.after → t ≺ a := by
  have ok' :
      List.Pairwise (· ≺ ·) (w.before ++ w.touching ++ w.after) := by
    simpa [w.order] using ok
  have ok'' :
      List.Pairwise (· ≺ ·)
        (w.before ++ (w.touching ++ w.after)) := by
    simpa [List.append_assoc] using ok'
  obtain ⟨_, ok_tail, _⟩ :=
    List.pairwise_append.1 ok''
  obtain ⟨_, _, cross_touch⟩ :=
    List.pairwise_append.1 ok_tail
  intro t ht a ha
  exact cross_touch (a := t) (b := a) ht ha

/-- Legality for Algo B rebuild:
`before ++ [glueMany curr touching] ++ after` is pairwise `(· ≺ ·)`. -/
lemma buildSplit_pairwise
    (curr : NR) {xs} (ok : List.Pairwise (· ≺ ·) xs)
    (w : SplitWitness curr xs)
    (htouch : ∀ t ∈ w.touching, NR.mergeable curr t) :
    List.Pairwise (· ≺ ·)
      (buildSplit curr w.before w.touching w.after) := by
  set g := glueMany curr w.touching with hg
  have ok_full :
      List.Pairwise (· ≺ ·) (w.before ++ w.touching ++ w.after) := by
    simpa [w.order] using ok
  have h_split1 :=
    List.pairwise_append.1 (by simpa [List.append_assoc] using ok_full)
  have ok_before : List.Pairwise (· ≺ ·) w.before := h_split1.1
  have ok_touch_after :
      List.Pairwise (· ≺ ·) (w.touching ++ w.after) := h_split1.2.1
  have h_split2 := List.pairwise_append.1 ok_touch_after
  have ok_touching : List.Pairwise (· ≺ ·) w.touching := h_split2.1
  have ok_after : List.Pairwise (· ≺ ·) w.after := h_split2.2.1
  have h_before_glue :
      ∀ b ∈ w.before, b ≺ g := by
    intro b hb
    have hb_curr : b ≺ curr := w.before_ok hb
    have hb_touch :
        ∀ t ∈ w.touching, b ≺ t := by
      intro t ht
      exact
        split_before_before_touch
          (curr := curr) (xs := xs) ok w hb ht
    have hb_glue_aux :
        ∀ (acc : NR) (ts : List NR),
            (∀ t ∈ ts, NR.mergeable acc t) →
            (∀ t ∈ ts, b ≺ t) →
            b ≺ acc →
            b ≺ glueMany acc ts := by
      intro acc ts
      induction ts generalizing acc with
      | nil =>
          intro _ _ hb_acc; simpa [glueMany] using hb_acc
      | cons t ts ih =>
          intro htouch_ts hbefore_ts hb_acc
          have htouch_head : NR.mergeable acc t := htouch_ts t (by simp)
          have hbefore_head : b ≺ t := hbefore_ts t (by simp)
          have hb_glued : b ≺ NR.glue acc t :=
            NR.before_glue hb_acc hbefore_head
          have htouch_tail :
              ∀ u ∈ ts, NR.mergeable (NR.glue acc t) u := by
            intro u hu
            have htu : NR.mergeable acc u := htouch_ts u (by simp [hu])
            exact mergeable_after_glue_step acc t u htouch_head htu
          have hbefore_tail :
              ∀ u ∈ ts, b ≺ u := by
            intro u hu
            exact hbefore_ts u (by simp [hu])
          have hb_tail :=
            ih (NR.glue acc t) htouch_tail hbefore_tail hb_glued
          simpa [glueMany] using hb_tail
    have hb_before_glue :=
      hb_glue_aux curr w.touching htouch hb_touch hb_curr
    simpa [hg] using hb_before_glue
  have h_glue_after :
      ∀ a ∈ w.after, g ≺ a := by
    intro a ha
    have hcurr_after : curr ≺ a := w.after_ok ha
    have htouch_to_a :
        ∀ t ∈ w.touching, t ≺ a := by
      intro t ht
      exact
        split_touch_before_after
          (curr := curr) (xs := xs) ok w ht ha
    have h_aux :
        ∀ (acc : NR) (ts : List NR),
            (∀ t ∈ ts, NR.mergeable acc t) →
            (∀ t ∈ ts, t ≺ a) →
            acc ≺ a →
            glueMany acc ts ≺ a := by
      intro acc ts
      induction ts generalizing acc with
      | nil =>
          intro _ _ hacc; simpa [glueMany] using hacc
      | cons t ts ih =>
          intro htouch_ts hbefore_ts hacc
          have htouch_head : NR.mergeable acc t := htouch_ts t (by simp)
          have ht_before : t ≺ a := hbefore_ts t (by simp)
          have h_glued : NR.glue acc t ≺ a :=
            NR.glue_before hacc ht_before
          have htouch_tail :
              ∀ u ∈ ts, NR.mergeable (NR.glue acc t) u := by
            intro u hu
            have htu : NR.mergeable acc u := htouch_ts u (by simp [hu])
            exact mergeable_after_glue_step acc t u htouch_head htu
          have hbefore_tail :
              ∀ u ∈ ts, u ≺ a := by
            intro u hu
            exact hbefore_ts u (by simp [hu])
          have ih_result :=
            ih (NR.glue acc t) htouch_tail hbefore_tail h_glued
          have ih_result' := ih_result
          simp [glueMany] at ih_result'
          exact ih_result'
    have h_glue := h_aux curr w.touching htouch htouch_to_a hcurr_after
    simpa [hg] using h_glue
  have pair_before_glue :
      List.Pairwise (· ≺ ·) (w.before ++ [g]) :=
    List.pairwise_append.mpr
      ⟨ok_before,
      List.pairwise_singleton (R := (· ≺ ·)) _,
        by
          intro b hb y hy
          rcases List.mem_singleton.1 hy with rfl
          exact h_before_glue b hb⟩
  have pair_final :
      List.Pairwise (· ≺ ·) ((w.before ++ [g]) ++ w.after) :=
    List.pairwise_append.mpr
      ⟨pair_before_glue,
        ok_after,
        by
          intro x hx a ha
          rcases List.mem_append.1 hx with hx | hx
          · exact
              split_before_before_after
                (curr := curr) (xs := xs) ok w hx ha
          · rcases List.mem_singleton.1 hx with rfl
            exact h_glue_after a ha⟩
  simpa [buildSplit, hg, List.append_assoc] using pair_final

/-- New insertion algorithm reusing the split/build pipeline. -/
def internalAddB (s : RangeSetBlaze) (r : IntRange) : RangeSetBlaze :=
  if hr : r.nonempty then
    let curr : NR := ⟨r, hr⟩
    let w := splitRanges curr s.ranges s.ok
    { ranges := buildSplit curr w.before w.touching w.after
      ok :=
        buildSplit_pairwise
          (curr := curr)
          (xs := s.ranges)
          (ok := s.ok)
          (w := w)
          (by
            intro t ht
            exact w.touch_ok ht) }
  else
    s

lemma internalAddB_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAddB s r).toSet = s.toSet ∪ r.toSet := by
  by_cases hr : r.nonempty
  · -- Nonempty range: unfold and compare via list sets.
    set curr : NR := ⟨r, hr⟩
    set w := splitRanges curr s.ranges s.ok
    have hbuild :
        rangesToSet (buildSplit curr w.before w.touching w.after) =
          curr.val.toSet ∪
            (rangesToSet w.touching ∪ rangesToSet w.before ∪ rangesToSet w.after) :=
      buildSplit_sets
          (curr := curr) (xs := s.ranges)
          (before := w.before) (touching := w.touching) (after := w.after)
          w.order
          (by
            intro t ht
            exact w.touch_ok ht)
    have hsplit :
        rangesToSet s.ranges =
          rangesToSet w.before ∪ rangesToSet w.touching ∪ rangesToSet w.after := by
      simp [w.order, rangesToSet_append, Set.union_assoc]
    have hcurr : curr.val.toSet = r.toSet := rfl
    have hs : s.toSet = rangesToSet s.ranges := toSet_eq_rangesToSet s
    have hne : ¬ r.empty := (IntRange.nonempty_iff_not_empty r).1 hr
    have htoSet :
        (internalAddB s r).toSet =
          curr.val.toSet ∪
            (rangesToSet w.touching ∪ rangesToSet w.before ∪ rangesToSet w.after) := by
      simp [internalAddB, hne, curr, w, toSet_eq_rangesToSet, hbuild]
    calc
      (internalAddB s r).toSet
          = curr.val.toSet ∪
              (rangesToSet w.touching ∪ rangesToSet w.before ∪ rangesToSet w.after) := htoSet
      _ = r.toSet ∪ (rangesToSet w.touching ∪ rangesToSet w.before ∪ rangesToSet w.after) := by
          simp [hcurr]
      _ = r.toSet ∪ rangesToSet s.ranges := by
          simp [Set.union_left_comm, Set.union_comm, hsplit]
      _ = r.toSet ∪ s.toSet := by
          rw [hs.symm]
      _ = s.toSet ∪ r.toSet := by
          simp [Set.union_comm]
  · -- Empty range: adding it changes nothing.
    have hEmpty : r.empty :=
      not_not.mp ((not_congr (IntRange.nonempty_iff_not_empty r)).1 hr)
    have hEmptySet : r.toSet = (∅ : Set Int) :=
      IntRange.toSet_eq_empty_of_hi_lt_lo hEmpty
    have hToSet :
        (internalAddB s r).toSet = s.toSet := by
      simp [internalAddB, hEmpty, toSet_eq_rangesToSet]
    calc
      (internalAddB s r).toSet
          = s.toSet := hToSet
      _ = s.toSet ∪ (∅ : Set Int) := by simp
      _ = s.toSet ∪ r.toSet := by simp [hEmptySet]

def internalAdd := internalAddB

@[simp] lemma internalAdd_toSet (s : RangeSetBlaze) (r : IntRange) :
    (internalAdd s r).toSet = s.toSet ∪ r.toSet :=
  internalAddB_toSet s r

lemma internalAddB_agrees_with_split_sets
    (s : RangeSetBlaze) (r : IntRange) (hr : r.nonempty) :
    let curr : NR := ⟨r, hr⟩
    let w := splitRanges curr s.ranges s.ok
    rangesToSet (buildSplit curr w.before w.touching w.after) =
      (internalAddB s r).toSet := by
  set curr : NR := ⟨r, hr⟩
  let w := splitRanges curr s.ranges s.ok
  have hsplit :
      rangesToSet s.ranges =
        rangesToSet w.before ∪ rangesToSet w.touching ∪ rangesToSet w.after := by
    simp [w.order, rangesToSet_append, Set.union_assoc]
  have hcurr : curr.val.toSet = r.toSet := rfl
  have hs : s.toSet = rangesToSet s.ranges := toSet_eq_rangesToSet s
  have hbuild :
      rangesToSet (buildSplit curr w.before w.touching w.after) =
        curr.val.toSet ∪
          (rangesToSet w.touching ∪ rangesToSet w.before ∪ rangesToSet w.after) :=
    buildSplit_sets (curr := curr) (xs := s.ranges)
      (before := w.before) (touching := w.touching) (after := w.after)
      w.order
      (by
        intro t ht
        exact w.touch_ok ht)
  have hne : ¬ r.empty := (IntRange.nonempty_iff_not_empty r).1 hr
  have htoSet :
      (internalAddB s r).toSet =
        curr.val.toSet ∪
          (rangesToSet w.touching ∪ rangesToSet w.before ∪ rangesToSet w.after) := by
    simp [internalAddB, hne, curr, w, toSet_eq_rangesToSet, hbuild]
  calc
    rangesToSet (buildSplit curr w.before w.touching w.after)
        = curr.val.toSet ∪
            (rangesToSet w.touching ∪ rangesToSet w.before ∪ rangesToSet w.after) := hbuild
    _ = rangesToSet s.ranges ∪ r.toSet := by
        simp [hcurr, hsplit, Set.union_comm]
    _ = s.toSet ∪ r.toSet := by
        rw [hs]
    _ = (internalAddB s r).toSet :=
        (internalAddB_toSet s r).symm

end

open IntRange
open scoped IntRange.NR

set_option linter.unusedTactic true

-- Core spec check (re-exports the simp lemma ensures Algo B meets the spec)
example (s : RangeSetBlaze) (r : IntRange) :
    (internalAdd s r).toSet = s.toSet ∪ r.toSet := by
  exact internalAdd_toSet s r

def rA : IntRange := ⟨0, 2⟩
def rB : IntRange := ⟨3, 5⟩     -- touches rA
def rC : IntRange := ⟨10, 12⟩   -- separate

def S0 : RangeSetBlaze :=
  let nrA : NR := ⟨rA, by decide⟩
  ⟨[nrA], by
    exact
      List.pairwise_singleton (R := (· ≺ ·)) (a := nrA)⟩

-- After inserting a touching range, union spec holds.
example : (internalAdd S0 rB).toSet = S0.toSet ∪ rB.toSet := by
  exact internalAdd_toSet S0 rB

-- After inserting a disjoint range, union spec still holds.
example : (internalAdd S0 rC).toSet = S0.toSet ∪ rC.toSet := by
  exact internalAdd_toSet S0 rC

end RangeSetBlaze
