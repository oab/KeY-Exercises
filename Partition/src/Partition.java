// Not done yet
class  Partition {
    
    public interface Predicate {
	boolean test(int x);
    }

    /*@
     @ public normal_behaviour
     @ requires in.length == out.length
     @ ensures (\forall int i; i < )...
     @*/
    static int partition(final int[] in, int[] out, Partition.Predicate p) {
	int low  = 0;
	int high = in.length-1;

	for(int i=0; i < in.length; i++) {
	    if(p.test(in[i])) {
		out[low++] = in[i];
	    } else {
		out[high--] = in[i];
	    }
	}
	
	return low;

    }
    
}
