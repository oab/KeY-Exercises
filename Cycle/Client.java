class Client {
    Cycle a, b;

    /*@ normal_behavior
      @ requires a != b;
      @ requires \invariant_for(a) && \invariant_for(b);
      @ requires \disjoint(a.footprint, b.footprint);
      @ ensures b.size() == \old(b.size());
      @ ensures \invariant_for(a) && \invariant_for(b);
      @*/
    void m() {
	a.add(5);
    }
}
