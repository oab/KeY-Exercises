public interface Cycle {
    //@ public model instance \locset footprint;
    //@ public accessible footprint: footprint;

    //@ public model instance \seq cycle;
    //@ public accessible cycle: footprint;
    
    //@ public instance invariant size() == cycle.length;
    //@ public instance invariant size() >= 1;
    
    //@ public accessible \inv: footprint;
 
    
    /*@ public normal_behavior
      @ ensures cycle == (size() == 1 ? \old(cycle)
      @                               : \seq_concat(\old(cycle[1..(size()-1)]),\old(cycle[0..0])));
      @ assignable footprint;
      @*/
    public Cycle /*@ pure @*/ next();
    
    /*@ public normal_behavior
      @ ensures cycle == ( \old(size()) == 1 ? \seq_concat( \seq_singleton(value), \old(cycle[0..0]) )
      @                                      : \seq_concat( \seq_concat(\old(cycle[0..0]),\seq_singleton(value) ), \old(cycle[1..(\old(size())-1)]) ) ); 
      @ ensures \new_elems_fresh(footprint);
      @ assignable footprint;
      @*/
    public Cycle add(int value);

    /*@ public normal_behavior
      @ ensures cycle == ( (\old(size()) == 1) ? cycle : (cycle[1..(\old(size())-1)]) );
      @ assignable footprint;
      @*/
    public Cycle remove();

    /*@ public normal_behavior
      @ ensures \result == cycle.length;
      @ accessible footprint;
      @*/
    public /*@ pure @*/ int size();

    /*@ public normal_behavior
      @ ensures \result == (int)(cycle[0]);
      @ accessible footprint;
      @*/
    public /*@ pure @*/ int value();


    // 1. replicate List Client example (prove modification of list a does not affect list b)
    // 2. extract cycle to list, use model field for representation

}
