/*
 * Here we make it slightly more difficult to write the loop invariant
 * when compared to the SentinelSearch.java problem.
 */

class SegmentSwap {

    /*@  public normal_behaviour
     @  requires 1 < a.length && a.length < 10 && 0 <= startLow && endHigh < a.length &&
     @           startLow <= endLow && startHigh <= endHigh && endLow < startHigh &&
     @           endLow-startLow == endHigh-startHigh;
     @  ensures (\forall int offset; 0 <= offset && offset <= endLow-startLow; 
     @           a[startLow+offset] == \old(a[startHigh+offset]) && 
     @           \old(a[startLow+offset]) == a[startHigh+offset]);
     @  assignable a[*];
    @*/
    static void swap1(int a[], final int startLow, final int endLow, final int startHigh, final int endHigh) throws Exception {
	int offset=0;
	/*@ loop_invariant (0 <= offset && offset <= endLow-startLow+1) &&
	  @ (\forall int o; 0 <= o && o < offset; 
	  @                  a[startLow+o] == \old(a[startHigh+o]) && \old(a[startLow+o]) == a[startHigh+o]) &&
	  @ (\forall int o; offset <= o && o <= endLow-startLow;
	  @                  a[startLow+o] == \old(a[startLow+o]) && a[startHigh+o] == \old(a[startHigh+o]));
          @                  
	  @ decreases (endLow-startLow+1) - offset;
	  @ assignable a[*];
	  @*/
	for(; offset <= endLow-startLow; offset++) {
	    int i = startLow + offset;
	    int j = startHigh + offset;
	    
	    int t = a[i];
	    a[i] = a[j];
	    a[j] = t;
	}
	
    }

    /*@  public normal_behaviour
     @  requires 1 < a.length && a.length < 10 && 0 <= startLow && startHigh+size-1 < a.length &&
     @           0 <= size && startLow+size-1 < startHigh;
     @  ensures (\forall int offset; 0 <= offset && offset < size; 
     @           a[startLow+offset] == \old(a[startHigh+offset]) && 
     @           \old(a[startLow+offset]) == a[startHigh+offset]);
     @  assignable a[*];
    @*/
    static void swap2(int a[], final int startLow, final int startHigh, final int size) throws Exception {
	int offset=0;
	/*@ loop_invariant (0 <= offset && offset <= size) &&
	  @ (\forall int o; 0 <= o && o < offset; 
	  @                  a[startLow+o] == \old(a[startHigh+o]) && \old(a[startLow+o]) == a[startHigh+o]) &&
	  @ (\forall int o; offset <= o && o < size;
	  @                  a[startLow+o] == \old(a[startLow+o]) && a[startHigh+o] == \old(a[startHigh+o]));
          @                  
	  @ decreases size - offset;
	  @ assignable a[*];
	  @*/
	for(; offset < size; offset++) {
	    int i = startLow + offset;
	    int j = startHigh + offset;
	    
	    int t = a[i];
	    a[i] = a[j];
	    a[j] = t;
	}
	
    }
 
    
}
