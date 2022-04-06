/* This is a warm-up exercise in writing some JML and attempting
 * to verify a sentinel search implementation correct. 
 */
class SentinelSearch {
    
     /*@ public normal_behaviour
      @   requires a.length >= 1;
      @   assignable a[a.length-1];
      @   ensures ((\exists int x; 0 <= x && x < a.length-1; a[x] == v) ? a[\result] == v 
      @                                                                 : \result == -1);
      @*/
    static int search(int[] a, int v) {      
	int i = 0;
	a[a.length-1] = v;

	/*@ loop_invariant (i >= 0) && (i < a.length) && (\forall int j; 0<=j && j<i; a[j] != v);
          @ decreases a.length - i;
	  @ assignable \strictly_nothing;
	  @*/
	while(a[i] != v) i++;

	if(i == a.length-1) i = -1;

	return i;
	
    }

      
     /*@ public normal_behaviour
      @   requires a.length >= 1 && a != null;
      @   assignable a[a.length-1];
      @   ensures ((\exists int x; 0 <= x && x < a.length-1; a[x] == v) ? a[\result] == v 
      @                                                                 : \result == -1);
      @ also
      @ public exceptional_behavior
      @ requires a == null;
      @ signals_only NullPointerException;
      @ assignable \nothing;
      @*/
    static int search2(/*@ nullable @*/ int[] a, int v) {      
	int i = 0;
	a[a.length-1] = v;

	/*@ loop_invariant (i >= 0) && (i < a.length) && (\forall int j; 0<=j && j<i; a[j] != v);
          @ decreases a.length - i;
	  @ assignable \strictly_nothing;
	  @*/
	while(a[i] != v) i++;

	if(i == a.length-1) i = -1;

	return i;
	
    }

    
}

   
