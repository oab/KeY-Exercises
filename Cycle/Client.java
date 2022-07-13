class Client {
    //@ private invariant \invariant_for(a) && \invariant_for(b);
    //@ private invariant \disjoint(this.*,a.footprint) && \disjoint(this.*,b.footprint);
   
    
    Cycle a, b;

    /*@ normal_behavior
      @ requires \invariant_for(singleton);
      @ requires \disjoint(singleton.footprint, a.footprint);
      @ requires \disjoint(singleton.footprint, b.footprint);
      @ requires \disjoint(singleton.footprint, this.*);
      @ requires singleton.size() == 1;
      @ requires singleton.value() == 0;
      @ ensures (\forall int i; 0 <= i && i<2; (int)(singleton.cycle[i]) == (int)((\seq_def int x; 0; 2; x)[i])) ;
      @*/
    void n(Cycle singleton) {
	singleton.add(1).add(2);
    }

    
    /*@ normal_behavior
      @ requires \invariant_for(singleton);
      @ requires \disjoint(singleton.footprint, a.footprint);
      @ requires \disjoint(singleton.footprint, b.footprint);
      @ requires \disjoint(singleton.footprint, this.*);
      @ requires singleton.size() == 1;
      @ requires singleton.value() == 0;
      @ ensures true ;
      @*/
    void nSimple(Cycle singleton) {
	singleton.add(1);
    }

    /*@ normal_behavior
      @ requires a != b;
      @ requires \disjoint(a.footprint, b.footprint);
      @ ensures b.size() == \old(b.size());
      @ ensures \invariant_for(a) && \invariant_for(b);
      @*/
    void m() {
	a.add(5);
    }
}
