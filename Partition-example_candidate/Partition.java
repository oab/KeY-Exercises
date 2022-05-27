/**
 * This example formalizes and verifies a simple partioning algorithm for arrays.
 * Given an integer array and a predicate the method int partition(int[],Predicate) 
 * will permute the array and return an integer indicating that the predicate holds
 * for any value at any valid index below this integer and the opposite for any
 * value at any valid index above this integer.
 * 
 * The proof requires manual interaction exactly as the example given in
 * page 564 of the KeY book. 
 * 
 * @author Ole Jørgen Abusdal
 */



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


class  Partition {

   
   /*@
     @ public normal_behaviour
     @ requires \invariant_for(p);
     @ ensures \dl_seqPerm(\dl_array2seq(in), \old(\dl_array2seq(in))) &&
     @           (\forall int i; 0 <= i && i < in.length; i < \result ? p.test(in[i]) : !p.test(in[i]));
     @ assignable in[*];
     @*/
    static int partition(final int[] in, final Predicate p) {
	  

	int low = 0;
	int high = in.length-1;

       /*@ 
	 @ loop_invariant  
         @ 0 <= low && low <= in.length && -1 <= high && high < in.length && low <= high+1 &&
         @
         @ (\forall int i; 0 <= i && i < low ; p.test(in[i])) &&
         @ (\forall int i; high < i && i< in.length; !p.test(in[i])) &&
	 @ \dl_seqPerm(\dl_array2seq(in), \old(\dl_array2seq(in)));
	 @
	 @ assignable in[*];
	 @
	 @ 
	 @ decreases high - low + 1;
	 @*/
  	while(low <= high) {

	    /*@ 
              @ loop_invariant 0 <= low && low <= in.length && low <= high+1 &&
	      @ (\forall int i; 0 <= i && i < low ; p.test(in[i]));
              @ decreases in.length + 1 - low;
	      @ assignable low;
	      @*/
	    while(low <= high && p.test(in[low])) low++;

	    /*@ 
              @ loop_invariant -1 <= high && high < in.length && low <= high+1 &&
	      @ (\forall int i; high < i && i < in.length; !p.test(in[i]));
              @ decreases high + 1;
	      @ assignable high;
	      @*/
	    while(low <= high && !p.test(in[high])) high--;
	      
	      if(low < high) {
		  int temp = in[low];
		  in[low] = in[high];
		  in[high] = temp;
		  low++;
		  high--;
		  
	      }

		
	}
	
	return low;

    }


    
}
