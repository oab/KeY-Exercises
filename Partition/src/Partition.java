// partition1 with passed predicate hard to close all goals on
// partition2 one with an inlined concrete predicate is manageable
// FIXME: it is silly to require in.length == out.length

// partition3 not done yet

//  [...,T,T,T,low,?, ... ,?, high,F,F,F,...]
//  low == #T, out.length - (high+1) == #F
//  i == low + out.length - (high+1)
//
class  Partition {

    public interface Predicate {

       /*@
	 @ public normal_behaviour
	 @ requires true;
	 @ assignable \strictly_nothing;
	 @ accessible \nothing;
	 @ ensures \result == (x < 5);
	 @*/
	boolean /*@ strictly_pure helper @*/ test(int x);
    }
	
   /*@
     @ public normal_behaviour
     @ requires in.length == out.length && in != out && \invariant_for(p);
     @ ensures (\forall int i; 0 <= i && i < in.length; (\exists int j; 0 <= j && j < out.length; in[i] == out[j] )) &&
     @         (\forall int i; 0 <= i && i < in.length; i < \result ? p.test(out[i]) : !p.test(out[i]) );
     @ assignable out[*];
     @*/
    static int partition1(final int[] in, int[] out, final Partition.Predicate p) {
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

   /*@
     @ public normal_behaviour
     @ requires in.length == out.length && in != out;
     @ ensures (\forall int i; 0 <= i && i < in.length; (\exists int j; 0 <= j && j < out.length; in[i] == out[j] )) &&
     @         (\forall int i; 0 <= i && i < in.length; i < \result ? out[i] < 5 : !(out[i] < 5) );
     @ assignable out[*];
     @*/
    static int partition2(final int[] in, int[] out) {
	int i = 0;
	int low  = 0;
	int high = in.length-1;

       /*@ 
	 @ loop_invariant 0 <= i && i <= in.length && 
	 @ 0 <= low && low <= in.length && -1 <= high && high < in.length &&
	 @ i == low + out.length - (high + 1)  &&
	 @ (\forall int x; 0 <= x && x < i; in[x] < 5 ? (\exists int l; 0 <= l && l < low; in[x] == out[l])
	 @                                             : (\exists int h; high < h && h < out.length; in[x] == out[h])) &&
	 @ (\forall int l; 0 <= l && l < low; out[l] < 5) &&
	 @ (\forall int h; high < h && h < out.length; !(out[h] < 5));
	 @ assignable out[*];
	 @                                               
	 @ decreases in.length - i;
	 @*/
	for(; i < in.length; i++) {
	    if(in[i] < 5) {
		out[low++] = in[i];
	    } else {
		out[high--] = in[i];
	    }
	}
	
	return low;

    }

   /*@
     @ public normal_behaviour
     @ requires \invariant_for(p);
     @ ensures (\forall int i; 0 <= i && i < in.length; (\exists int j; 0 <= j && j < in.length; in[i] == \old(in[j]) )) &&
     @         (\forall int i; 0 <= i && i < in.length; i < \result ? p.test(in[i]) : !p.test(in[i]) );
     @ assignable in[*];
     @*/
    static int partition3(final int[] in, final Partition.Predicate p) {
	int low = 0;
	int high = in.length-1;

       /*@ 
	 @ loop_invariant  0 <= low && low <= in.length && -1 <= high && high < in.length &&
	 @ (low < high ==> (\forall int x; low < x && x < high; in[x] == \old(in[x]))) &&
	 @ (\forall int x; 0 <= x && x < low; (\exists int i; 0 <= i && i < in.length; in[x] == \old(in[i]))) &&
         @ (\forall int x; high < x && x < in.length; (\exists int i; 0 <= i && i < in.length; in[x] == \old(in[i]))) &&
	 @ (\forall int l; 0 <= l && l < low; p.test(in[l])) &&
	 @ (\forall int h; high < h && h < in.length; !p.test(in[h]));
	 @ assignable in[*];
	 @                                               
	 @ decreases high - low;
	 @*/
  	while(low < high) {
	    
            /*@ ensures low == in.length || !p.test(in[low]);
	      @ signals_only \nothing;
	      @*/
	    {
	      while(low < in.length && p.test(in[low])) low++;
	    }
	    
            /*@ ensures high == -1 || p.test(in[high]);
              @ signals_only \nothing;
	      @*/
	    {
	      while(0 < high && !p.test(in[high])) high--;
	    }


	    if(low < high) {
		/*@
		  @ ensures in[low] == \old(in[high]) && in[high] == \old(in[low]);
		  @ signals_only \nothing;
		  @*/
		{
		    int temp = in[low];
		    in[low] = in[high];
		    in[high] = temp;
		    low++;
		    high--;
		}
	    }

		
	}
	
	return low;

    }


    
}
