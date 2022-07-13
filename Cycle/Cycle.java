public interface Cycle {
    //@ public model instance \locset footprint;
    //@ public accessible footprint: footprint;

    //@ public model instance \seq cycle;
    //@ public accessible cycle: footprint;
    
    //@ public instance invariant cycle.length >= 1;
    //@ public instance invariant (\forall Cycle c; c != this; \disjoint(footprint, c.footprint));
    
    //@ public accessible \inv: footprint;
 
    // if cycle is eL then it remains so, but returns Le
    /*@ public normal_behavior
      @ ensures cycle == \old(cycle);
      @ ensures \result.cycle == \seq_concat( \old(cycle[1..cycle.length]), \old(cycle[0..1]) );
      @ assignable footprint;
      @*/
    public Cycle next();

    // if the added is v and cycle is eL then cycle becomes evL, returns vLe
    /*@ public normal_behavior
      @ ensures cycle == \seq_concat( \seq_concat(\old(cycle[0..1]), \seq_singleton(value) ), \old(cycle[1..size()])); 
      @ ensures \result.cycle == \seq_concat( \seq_concat(\seq_singleton(value), \old(cycle[1..size()])), \old(cycle[0..1]) );
      @ ensures \new_elems_fresh(footprint);
      @ ensures \invariant_for(\result);
      @ ensures \fresh(\result);
      @ ensures \fresh(\result.footprint);
      @ assignable footprint;
      @*/
    public Cycle add(int value);

    // if the cycle is size 1 do nothing, otherwise cycle is eL and becomes L
    /*@ public normal_behavior
      @ requires cycle.length == 1;
      @ assignable \strictly_nothing;
      @ also
      @ public normal_behavior
      @ requires cycle.length > 1;
      @ ensures cycle == \old(cycle[1..cycle.length]);
      @ assignable footprint;
      @*/
    public Cycle remove();

    /*@ public normal_behavior
      @ ensures \result == cycle.length;
      @ accessible footprint;
      @*/
    public /*@ strictly_pure @*/ int size();

    /*@ public normal_behavior
      @ ensures \result == cycle[0];
      @ accessible footprint;
      @*/
    public /*@ strictly_pure @*/ int value();

 
}
