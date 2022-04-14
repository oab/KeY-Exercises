//  Not complete
//  [...,T,T,T,low,?, ... ,?, high,F,F,F,...]
//  low == #T, out.length - (high+1) == #F
//  i == low + out.length - (high+1)
//
class  Partition {
    
    public interface Predicate {
	boolean test(int x);
    }

   /*@
     @ public normal_behaviour
     @ requires in.length == out.length;
     @ ensures (\forall int i; 0 <= i && i < in.length; (\exists int j; 0 <= j && j < out.length; in[i] == out[j] )) && 
     @         (\forall int i; 0 <= i && i < in.length; i < \result ? p.test(out[i]) : !p.test(out[i]) );
     @ assignable out[*];
     @*/
    static int partition(final int[] in, int[] out, final Partition.Predicate p) {
	int i = 0;
	int low  = 0;
	int high = in.length-1;

	/*@ 
	  @ loop_invariant 0 <= i && i <= in.length && 
          @ 0 <= low && low <= in.length && -1 <= high && high < in.length &&
          @ i == low + out.length - (high + 1)  &&
          @ (\forall int x; 0 <= x && x < i; p.test(in[x]) ? (\exists int l; 0 <= l && l < low; in[x] == out[l])
          @                                                : (\exists int h; high < h && h < out.length; in[x] == out[h])) &&
	  @ (\forall int l; 0 <= l && l < low; p.test(out[l])) &&
          @ (\forall int h; high < h && h < out.length; !p.test(out[h]));
	  @ assignable out[*];
	  @                                               
	  @ decreases in.length - i;
	  @*/
	for(; i < in.length; i++) {
	    if(p.test(in[i])) {
		out[low++] = in[i];
	    } else {
		out[high--] = in[i];
	    }
	}
	
	return low;

    }
    
}
