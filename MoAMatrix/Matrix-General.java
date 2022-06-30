class Matrix {
    /*
     * We hope to prove two alg. for computing 
     * the matrix product MN = MK*KN equivalent with KeY. 
     * for arbitrary M,N and K ? 
     */
    
    
    // We imagine someone wrote this
    /*@
      @ public normal_behavior
      @ assignable \nothing;
      @ diverges true;
      @*/
    public static int[] mul1(int[] a, int[] b,int M, int N, int K) {

	assert a.length == M*K && b.length == K*N;

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
      @ diverges true;
      @*/
    public static int[] mul2(int[] a, int[] b, int M, int N, int K) {
        assert a.length == M*K && b.length == K*N;
	
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


    /*@
      @ public normal_behavior
      @ ensures \result == true;
      @ requires a.length == M*K && b.length == K*N; 
      @ diverges true;
      @*/
    public static boolean check(int a[],int b[], int M, int N, int K) {
	boolean check = true;
	int[] left  = mul1(A,B);
	int[] right = mul2(A,B);
	for(int i=0;i<MN;i++) check = check && left[i] == right[i];
	return check;
    }

    // might there be a way to do this for arbitrary arguments?
    

}
