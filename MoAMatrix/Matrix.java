class Matrix {
    /*
     * As example we use the matrix product MN = MK*KN
     * seen below. We hope to prove two alg. for computing
     * it as equivalent with KeY. 
     *
     * | 1  2  3|       | 22  28|
     * | 4  5  6||1 2|  | 49  64|
     * | 7  8  9||3 4| =| 76 100|
     * |10 11 12||5 6|  |103 136|
     * |13 14 15|       |130 172|
     *
     * Can we prove alg. equivalent for arbitrary M,N and K ? 
     */
    
    final static int M = 5;
    final static int K = 3;
    final static int N = 2;
    final static int MN = M*N;
    
    final static int[] A = new int[M*K];
    final static int[] B = new int[K*N];

    static {
	int v=1;
	for(int i=0;i<A.length;i++) A[i]=v++;
	v=1;
	for(int i=0;i<B.length;i++) B[i]=v++;
    }

    // We imagine someone wrote this
    /*@
      @ public normal_behavior
      @ assignable \nothing;
      @*/
    public static int[] mul1(int[] a, int[] b) {

	int[] out = new int[M*N];
	int[] tmp = new int[N*K];

	for(int i=0; i<N; i++) {
	    for(int j=0; j<K; j++) {
		tmp[i*K+j] = b[j*N+i];
		
	    }
	}
	
	for(int i=0;i<M;i++) {
	    for(int j=0;j<N;j++) {
		for(int k=0;k<K;k++) {
		    out[i*N+j] += a[i*K+k] * tmp[j*K+k];
	        }
	    }
	}
	
	return out;
    }

    // Then another implemenation is given (e.g. derived from MoA)
    /*@
      @ public normal_behavior
      @ assignable \nothing;
      @*/
    public static int[] mul2(int[] a, int[] b) {
	int[] out = new int[M*N];
	for(int i=0;i<M;i++) {
	    for(int j=0;j<N;j++) {
		for(int k=0;k<K;k++) {
		    out[i*N+j] += a[i*K+k] * b[k*N+j];
	        }
	    }
	}
	return out;
    }

    // A concrete proof obligation
    /*@ public normal_behavior
      @ ensures \result == true;
      @ assignable \strictly_nothing;
      @
      @ model boolean mul1_eq_mul2() {
      @   return (\forall int i; 
      @           0 <= i && i < MN; 
      @           mul1(A,B)[i] == mul2(A,B)[i] );
      @ }
      @*/


    /*@
      @ public normal_behavior
      @ ensures \result == true;
      @*/
    public static boolean check() {
	boolean check = false;
	int[] left  = mul1(A,B);
	int[] right = mul2(A,B);
	for(int i=0;i<MN;i++) check = check && left[i] == right[i];
	return check;
    }

    // might there be a way to do this for arbitrary arguments?
   

}
