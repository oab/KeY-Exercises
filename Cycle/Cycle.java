public interface Cycle {
    //@ public model instance \locset footprint;
    //@ public accessible footprint: footprint;

    //@ public model instance \seq cycle;
    //@ public accessible cycle: footprint;
    
    //@ public instance invariant size() == cycle.length;
    //@ public instance invariant size() >= 1;
    
    //@ public accessible \inv: footprint;
 
    // if cycle is eL then it remains so, but returns Le
    /*@ public normal_behavior
      @ ensures cycle == \old(cycle);
      @ ensures \result.cycle == \seq_concat( \old(cycle[1..\old(size())]), \old(cycle[0..1]) );
      @ assignable footprint;
      @*/
    public Cycle /*@ pure @*/ next();

    // if the added is v and cycle is eL then cycle becomes evL, returns vLe
    /*@ public normal_behavior
      @ ensures cycle == \seq_concat( \seq_concat(\old(cycle[0..1]), \seq_singleton(value) ), \old(cycle[1..\old(size())])); 
      @ ensures \result.cycle == \seq_concat( \seq_concat(\seq_singleton(value), \old(cycle[1..\old(size())])), \old(cycle[0..1]) );
      @ ensures \new_elems_fresh(footprint);
      @ assignable footprint;
      @*/
    public Cycle add(int value);

    // if the cycle is size 1 do nothing, otherwise cycle is eL and becomes L
    /*@ public normal_behavior
      @ ensures cycle == ( (\old(size()) == 1) ? cycle : (cycle[1..\old(size())]) );
      @ assignable footprint;
      @*/
    public void remove();

    /*@ public normal_behavior
      @ ensures \result == cycle.length;
      @ accessible footprint;
      @*/
    public /*@ pure @*/ int size();

    /*@ public normal_behavior
      @ ensures \result == cycle[0];
      @ accessible footprint;
      @*/
    public /*@ pure @*/ int value();

 
}
