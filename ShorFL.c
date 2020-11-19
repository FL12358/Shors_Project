#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <assert.h>
#include <complex.h>
#include <limits.h>
#include <time.h>
#include <getopt.h>

/*  version     =   1.0.8
*   author      =   Frederick W Liardet
*   date        =   2020.02.25
*
*   ShorFL takes a target value and optionally the numbers of qubits allocated for each register as inputs. 
*   It then attempts to factor the target value into its two prime factors. Due to how the algorithm works a 
*   random value 'a' is generated and in some cases this value will be able to find the factors without using 
*   any of the 'quantum' part of the algorithm. 
*
*   The optimal values for the L and M qubits registers are given by: (where C is the target value)
*            M >= log_2(C)
*            L >= log_2(C^2)
*    
*   The program takes in command line arguments:
*   -c [int]    Target value to output prime factors of
*   -l [int]    Number of qubits assigned to L register (optional)
*   -m [int]    Number of qubits assigned to M register (optional)
*   -a [int]    'a' value to use for the first attempt of the shor's algorithm calculation
*
*   Example compile command:
*       |$ gcc -Wall ShorFL.c -lm -o shorProg
*
*   Examples of using the program:  
*       |$ ./shorProg -c 15 -l 8 -m 4 -a 7
*
*   This generates output:
*       | Trying with 'a' value: 7
*       | 
*       | Applying Hadamard gates to L register...                DONE
*       | Applying modular multiplication gates on M register...  DONE
*       | Creating inverse quantum fourier transform...           DONE
*       | Applying IQFT...                                        DONE
*       | Finding output period...                                DONE
*       | 
*       | SUCCESS: Factors of 15 are: 5,3
*   Note that the '-l' and '-m' options are redundant in this case as 8 and 4 are the optimal values which 
*   would be calculated if these arguments were omitted. 
*
*   Some example values which will run and execute the quantum part of shors algorithm are as follows:
*       _________________
*       |C  |L  |M  |a  |
*       |15 |8  |4  |7  |
*       |21 |9  |5  |7  |
*       |57 |12 |6  |5  |
*       |87 |13 |7  |59 |
*
*/


const int ITERNO = 1000; // Number of quantum measurements to be made on the state vector

#ifndef M_PI // If M_PI is not defined in math.h
    #define M_PI 3.14159265358
#endif

#define MATACCESS(M,t,x,y) (M.t[(x) + (y)*M.rank]) // mat.type[x+y*mat.rank]       type => colIndex,vals
/*  Macro to acsess matrix and sparse matrix values, M is the matrix, t is the type:
    Normal matrix: t => vals, x,y => coordinates of value
    Sparse matrix: t => vals or colIndex, x => row, y => index of the value on its row (between 0 and valsPerRow-1)
*/

/// Struct Definitions ///

typedef struct{ // Sparse Matrix
    long rank;
    int valsPerRow;
    long* colIndex;    // valsPerRow*n matrix of non-zero columns for each row
    double complex* vals;  // valsPerRow*n matrix of values for each colNo index
} Smatrix;


typedef struct{ // Full Matrix
    long rank;  // All matrices used are square so only one value needed here (rank * rank matrix)
    double complex* vals;
} Matrix;


typedef struct{ // Vector
    long rank;
    double complex* vals;
} Vector;

typedef struct{ // Contains the size of the L and M registers
    int lBits;
    int mBits;
} Register;

/// Utility Functions ///

static void* Xmalloc(size_t bytes){
/*  Functionally the same as malloc(), but throws error when memory allocation fails
*/
    void* retVal = malloc(bytes);
    if(retVal){
        return retVal;
    }
    fprintf(stderr, "\nERROR: Failed to allocate memory\n");
    exit(EXIT_FAILURE);
}

static int RegisterTotal(Register reg){
/*  Returns the sum of the L and M register sizes
*/
    return reg.lBits + reg.mBits;
}

static long IntPow(long base, long power){
/*  Calculates Integer powers, uses squaring method 
*/  
    if(power == 0) return 1;
    if(power == 1) return base;
    if(power%2 == 0) return IntPow(base*base, power/2);
    if(power%2 == 1) return base*IntPow(base*base, (power-1)/2);

    return base;
}


static int IntegerExponentModulus(int base, int exponent, int modNo){
/*  Calculates base^(2^exponent) % modNo without integer overflow issues caused by large integer values
*/
    if(exponent){
        return (int)IntPow(IntegerExponentModulus(base, exponent-1, modNo), 2)%modNo;
    }

    return base%modNo;
}


static int Gcd(int a, int b){
/*  Returns greatest common denominator of integers 'a' and 'b'
*/
    if(a == 0){
        return b;
    }

    return Gcd((b%a), a);
}


static int IsPrime(int val){
/*  Retuns 1 if val is a prime, 0 elsewhere
    Slow algorithm, but fast enough for range of numbers in this project
*/  
    for(int i = 2 ; i <= ceil(sqrt(val)); i++){ // starts from 2 as 0 and 1 are impossible/trivial
        if(val%i == 0){
            return 0;
        }
    }
    return 1;
}


static double RandZeroOne(){
/*  Returns random double float number between 0 and 1
*/
    return rand()/(RAND_MAX + 1.);
}


/// Binary Manipulation Functions ///

static int BinValFromInt(long intVal, int bit){
/*  Returns the binary value of the 'bit'th bit in the integer 'intVal'
*/
    return (intVal>>bit) & 1; // Right shift until 'bit'th bit is in the ones place, then AND gate with 1
}


static int RegisterReturnL(int value, Register reg){
/*  Returns the value of the L register, creates the value from the binary values of the top bits
    Return value is an integer (but is cast to double for calculations)
*/  
    int retVal = 0;

    for(int i = 0; i < reg.lBits; i++){
        retVal += (int)IntPow(2, i)*BinValFromInt(value, RegisterTotal(reg)-1-i);
    }

    return retVal;
}


/// Sparse Matrix General Functions ///

static Smatrix SMatrixInit(long rank, int valsPerRow){
/*  Initialises Smatrix with a row length of 2 and a column length of 'rank'
*/
    Smatrix mat;
    mat.rank = rank;
    mat.valsPerRow = valsPerRow;
    mat.colIndex = Xmalloc(valsPerRow*rank*sizeof(long));
    mat.vals = Xmalloc(valsPerRow*rank*sizeof(double complex));

    for(long i = 0; i < rank; i++){   // sets defaults to 0
        for(int j = 0; j < valsPerRow; j++){
            MATACCESS(mat,colIndex,i,j) = 0;
            MATACCESS(mat,vals,i,j) = 0.0;
        }
    }

    return mat;
}


static void SMatrixFree(Smatrix mat){
/*  Frees 2D array created by Initialise2DArray()
*/
    free(mat.colIndex);
    free(mat.vals);
}


/// Matrix General Functions ///

static Matrix MatrixInit(long rank){
/*  Creates Matrix with all values set to zero
*/
    Matrix mat;
    mat.rank = rank;
    mat.vals = Xmalloc(rank*rank*sizeof(double complex));

    for(long i = 0; i < rank; i++){ // sets values to 0
        for(long j = 0; j < rank; j++){
            MATACCESS(mat,vals,i,j) = 0.0 + 0.0*I;
        }
    }

    return mat;
}


static void MatrixFree(Matrix mat){
/*  Frees matrix created by 'MatrixInit()'
*/
    free(mat.vals);
}


/// Vector General Functions ///

static Vector VectorInit(long rank){
/*  Creates vector of 'rank' length
    Memory for Vector vec is freed by 'free(vec.vals);'
*/
    Vector vec;
    vec.rank = rank;
    vec.vals = Xmalloc(vec.rank*sizeof(double complex));

    for(long i = 0; i < rank; i++){
        vec.vals[i] = 0.0 + 0.0*I;
    }

    return vec;
}


static Vector NormVector(Vector vec){
/*  Normalises vector 'vec', returns normalised vector
*/
    double mag = 0;
    for(long i = 0; i < vec.rank; i++){   // Calculate magnitude of vector
        mag += pow(vec.vals[i], 2);
    }
    assert(mag != 0);
    mag = sqrt(mag);

    for(long i = 0; i < vec.rank; i++){
        vec.vals[i] /= mag;
    }

    return vec;
}


static Vector SMatrixVectorProduct(Smatrix mat, Vector vec){
/*  Returns vector product of sparse matrix 'mat' and vector 'vec' i.e. --> retVec = mat*vec
*/
    Vector retVec = VectorInit(vec.rank);

    for(long i = 0; i < retVec.rank; i++){
        for(int j = 0; j < mat.valsPerRow; j++){
            retVec.vals[i] += vec.vals[MATACCESS(mat,colIndex,i,j)] * MATACCESS(mat,vals,i,j);
        }
    }

    free(vec.vals);
    return retVec;
}


/// Quantum Gate Functions ///

static Smatrix GateHadamard(int targetBit, Smatrix mat){
/*  Returns sparse hadamard gate for gate 'mat', with target bit 'targetBit'
*/
    long xIndex = 0; // Indices of hadamard matrix
    Matrix matHadamard = MatrixInit(2);

    MATACCESS(matHadamard,vals,0,0) =  1.0;    // Hadamard Matrix:
    MATACCESS(matHadamard,vals,1,0) =  1.0;    //  1   1
    MATACCESS(matHadamard,vals,0,1) =  1.0;    //  1  -1
    MATACCESS(matHadamard,vals,1,1) = -1.0;

    for(long i = 0; i < mat.rank; i++){ // Loop over rows
        if(BinValFromInt(i,targetBit)){ // Find value of diagonal element
            xIndex = 1; // x Index = y Index for diagonal element 
        }
        else{   // If targetBit'th binary value is 0
            xIndex = 0;
        }
        // diagonal value
        MATACCESS(mat,vals,i,0) = MATACCESS(matHadamard,vals,xIndex,xIndex);
        MATACCESS(mat,colIndex,i,0) = i; 

        // non-diagonal value
        long col2 = i ^ (1 << targetBit); // 2nd column value is 'i' but has one changed bit at the 'targetBit' place
        long yIndex = BinValFromInt(col2, targetBit); // find y index of original Hadamard matrix (targetBit'th bit of col2)
        MATACCESS(mat,vals,i,1) = MATACCESS(matHadamard,vals,xIndex,yIndex);
        MATACCESS(mat,colIndex,i,1) = col2;
    }

    MatrixFree(matHadamard);
    return mat;
}


static Smatrix GateModularMult(int mBits, int controlBit, int targetVal, int aVal, Smatrix mat){
/*  Returns a Modular Multiplication gate based on control and target bits and the selected "a" value
*/
    int multiplier = IntegerExponentModulus(aVal, controlBit-mBits, targetVal);

    for(long k=0; k < mat.rank; k++){  // loop over gate columns (k as in paper)
        MATACCESS(mat,vals,k,0) = 1.0; // Value is always 1, only location changes
        
        if(~BinValFromInt(k, controlBit)){ // if controlBit'th bit of k is zero
            MATACCESS(mat,colIndex,k,0) = k; // Value on diagonal
        }
        if(BinValFromInt(k, controlBit)){
            int mVal = k & (IntPow(2, mBits) - 1);

            if(mVal >= targetVal){
                MATACCESS(mat,colIndex,k,0) = k; // Value on diagonal
            }
            else if(mVal < targetVal){
                int mValNew = (multiplier*mVal)%targetVal;
                int kNew = k >> mBits;
                kNew <<= mBits; // set rightmost bits to 0
                kNew |= mValNew;  // set rightmost bits to mValNew
                MATACCESS(mat,colIndex,k,0) = kNew;
            }
        }
    }

    return mat;
}


static Smatrix GateControlledPhase(int controlBit, int targetBit, double phase, Smatrix mat){
/*  Returns a controlled phase shift gate based on target and control bits and the phase shift value
*/
    Matrix matCPhase = MatrixInit(4);
                                            //  Controlled Phase Shift Matrix:
    MATACCESS(matCPhase,vals,0,0) = 1.0;           //  1   0   0   0  
    MATACCESS(matCPhase,vals,1,1) = 1.0;           //  0   1   0   0
    MATACCESS(matCPhase,vals,2,2) = 1.0;           //  0   0   1   0
    MATACCESS(matCPhase,vals,3,3) = cexp(I*phase); //  0   0   0   exp(i*phase)

    for(int i = 0; i < mat.rank; i++){
        int index = 2*BinValFromInt(i, controlBit) + BinValFromInt(i, targetBit); // get index of CPhase matrix, between 0 and 3
        MATACCESS(mat,vals,i,0) = MATACCESS(matCPhase,vals,index,index);
        MATACCESS(mat,colIndex,i,0) = i;    // Diagonal matrix
    }

    MatrixFree(matCPhase);
    return mat;
}


/// Shors Algorithm Functions ///

static int QuantumMeasurement(Vector vec){
/*  Performs random meaurement of vector 'vec' and returns the index of the measured element
*/
    double r = RandZeroOne();
    double q = 0;

    for(long i = 0; i < vec.rank; i++){
        q += pow(vec.vals[i], 2);
        if(r < q){
            return i;
        }
    }

    fprintf(stderr,"ERROR: Invalid vector encountered\n");
    exit(EXIT_FAILURE);
}


static Vector ShorInitRegister(Register reg){
/*  Initialise quantum register, with lowest bit set to 1
*/
    long numStates = IntPow(2, RegisterTotal(reg));
    Vector state = VectorInit(numStates);
    state.vals[1] = 1.0 + 0.0*I;  // corresponds to m_0 = |1>

    return NormVector(state);
}


static Vector ShorHadamardLReg(Vector state, Register reg){
/*  Applies a Hadamard gate to the top N qubits (L qubit register)
*/  
    Smatrix hGate = SMatrixInit(state.rank, 2); // Hadamard gate has two values per row
    for(int i = (RegisterTotal(reg)-1); i >= (reg.mBits); i--){
        hGate = GateHadamard(i, hGate);
        state = SMatrixVectorProduct(hGate, state);
    }

    SMatrixFree(hGate);
    return state;
}


static Vector ShorModularMult(Vector state, Register reg, int targetVal, int a){
/*  Performs Modular multiplication on m register, controlled by l register
*/
    Vector retState = VectorInit(state.rank);
    retState = state; // set up so loop multiplication easier
    Smatrix gateS = SMatrixInit(state.rank, 1);

    for(int i = reg.mBits; i < RegisterTotal(reg); i++){
        gateS = GateModularMult(reg.mBits, i, targetVal, a, gateS);
        retState = SMatrixVectorProduct(gateS, retState);
    }

    SMatrixFree(gateS);
    return retState;
}


static Vector ShorIQFTGatesApply(Vector state, int thisRecNumGates, Register reg, Smatrix* gate){
/*  Returns array of sparse matrices which performs the inverse quantum fourier transform (IQFT)
    thisRecNumGates starts equal to L register size and decreases to zero
*/
    if(thisRecNumGates == 0){ // If final recursion
        return state;
    }

    int highestBit = reg.mBits+thisRecNumGates-1; // Highest bit index for this section of gates (control bit for phase shift)
    int targetBit = highestBit; // target bit for gate generation

    for(int i = 0; i < thisRecNumGates; i++){ // for each gate in current section
        if(i == 0){ // 1st gate in each level is a Hadamard gate
            gate[1] = GateHadamard(targetBit, gate[1]);
            state = SMatrixVectorProduct(gate[1], state);
        }
        else{ // All other gates in a section are phase shift gates
            targetBit--;
            double phase = M_PI / IntPow(2, i); // generate phase shift value
            gate[0] = GateControlledPhase(highestBit, targetBit, phase, gate[0]);
            state = SMatrixVectorProduct(gate[0], state);
        }
    }

    return ShorIQFTGatesApply(state, thisRecNumGates-1, reg, gate);
}


static Vector ShorIQFTGatesInit(Vector state, Register reg){
/*  Sets up IQFT generation, returns the modified state vector
*/
    Smatrix* gate = Xmalloc(2*sizeof(Smatrix));
    gate[0] = SMatrixInit(state.rank, 1); // Phase shift gate
    gate[1] = SMatrixInit(state.rank, 2); // Hadamard gate

    state = ShorIQFTGatesApply(state, reg.lBits, reg, gate);

    SMatrixFree(gate[0]);
    SMatrixFree(gate[1]);
    free(gate);
    return state;
}


static int ShorPeriodCalculation(Vector state, Register reg){
/*  Return period of IQFT calculation 
*/
    int* measureCount = Xmalloc(state.rank*sizeof(int)); // number of measurements of each state
    int numMeasure = 0; // number of different measurements produced

    state = NormVector(state); // normalise state vector

    for(long i = 0; i < state.rank; i++){ // set up measureCount array
        measureCount[i] = 0;
    }

    for(int i = 0; i < ITERNO; i++){ // Perform ITERNO number of measurements
        measureCount[QuantumMeasurement(state)] += 1;
    }

    for(long i = 0; i < state.rank; i++){ // Calculates number of valid measurement states
        if(measureCount[i] != 0){
            numMeasure++;
        }
    }
    
    double xBarVals[numMeasure]; // Number of meaureed xBar values
    int xBarIndex = 0;

    for(long i = 0; i < state.rank; i++){
        if(measureCount[i] != 0){ // if state has been measured at least once
            xBarVals[xBarIndex++] = (double)RegisterReturnL(i, reg) / IntPow(2, reg.lBits); // Output xBar/2^L values
        }
    }
    free(measureCount);

    double lowestXVal = INT_MAX;    // Frequency of array
    for(int i = 0; i < xBarIndex; i++){
        if(lowestXVal > xBarVals[i] && xBarVals[i] != 0){ // finds lowest non-zero value
            lowestXVal = xBarVals[i];
        }
    }

    return (int)1/lowestXVal; // Return period value
}


static void PrintTime(long time){
/*  Prints the change in time since 'time'
*/
    fprintf(stderr, "DONE (%.3lfs)\n", (double)(clock()-time)/CLOCKS_PER_SEC);
}

static int ShorsQuantumPart(int targetVal, Register reg, int a){
/*  Performs quantum part of Shors algorithm (period finding)
*/
    // Init Register
    fprintf(stderr, "\n");   
    fprintf(stderr, "Initalising registers...\t\t\t\t");
    clock_t time = clock();
    Vector state = ShorInitRegister(reg);
    PrintTime(time);

    // Apply Hadamard gate on L register
    fprintf(stderr, "Applying Hadamard gates to L register...\t\t"); 
    time = clock();
    state = ShorHadamardLReg(state, reg);
    PrintTime(time);
    
    // Apply Modular Multiplication on M register
    fprintf(stderr, "Applying modular multiplication gates on M register...\t");   
    time = clock();
    state = ShorModularMult(state, reg, targetVal, a);
    PrintTime(time);
    
    // Apply Inverse Quantum Fourier Transform
    fprintf(stderr, "Applying IQFT...\t\t\t\t\t"); 
    time = clock();
    state = ShorIQFTGatesInit(state, reg);
    PrintTime(time);
    
    // Get period from L register
    fprintf(stderr, "Finding output period...\t\t\t\t"); 
    time = clock();
    int p = ShorPeriodCalculation(state, reg);
    PrintTime(time);

    free(state.vals);
    return p;
}


static int CheckIfPrimeFactor(int targetNo){
/*  Check if target is power of lower integer and print out the factors
    Returns 1 if target factors are found, 0 otherwise 
*/
    for(int i = 2; i < targetNo; i++){    
        int temp = 1; // test value
        int power = 0; // the power that the value is raised to
        while(temp < targetNo){
            temp *= i;
            power++;
        }
        if(temp == targetNo){ // if target is a power of lower integer
            printf("SUCCESS: Factors of %i are : ", targetNo);
            for(int k = 0; k < power; k++){
                printf("%i ", i);
            }
            printf("\n");
            return 1;
        }
    }

    return 0;
}


static int CheckRegisterSize(int size, int paramVal, char regType){
/*  Checks the size of a register and returns the size with a warning if below optimal value
    paramVal is either equal to target integer or target integer squared
    Returns optimal value if size is zero
*/
    if(size == 0){
        size = ceil(log2(paramVal)); // set to ideal
        printf("Number of %c Qubits set to: %i\n", regType, size);
    }
    else if(paramVal > IntPow(2, size)){
        int target = (int)ceil(log2(paramVal));
        fprintf(stderr, "WARNING: Not enough L Qubits allocated: %i (Ideal mimumum number: %i)\n", size, target);
    }

    return size;
}


static int* FactorCorrection(int* factors, int targetVal){
/* If only one of the found factors is correct, calculate other factor 
*/
    if(factors[0]*factors[1] == targetVal){ // if correct factors
        return factors;
    }
    for(int i = 0; i < 2; i++){
        if(factors[i] < 0){ // Correct negative factors
            factors[i] = -factors[i];
        }
        if(targetVal/factors[i] != 1 && targetVal/factors[i] != targetVal){ // if only one of the factors is correct
            factors[(i+1)%2] = targetVal/factors[i]; // (i+1)%2 selects other factor
        }    
    }

    return factors;
}


static int ShorsMainWrapper(int targetNo, Register reg, int aVal); // Function prototype


static int FactorSuccess(int* factors, int targetNo){    
/*  print correct factors and check if either of them are prime
    If a factor is not prime run algorithm again with that factor
*/
    printf("SUCCESS: Factors of %i are: %i,%i\n\n",targetNo, factors[0], factors[1]);

    for(int i = 0; i < 2; i++){   // If a factor found is not a prime number
        if(!IsPrime(factors[i]) && factors[i] > 2){
            printf("NOTE: %i is not prime, finding factors:\n", factors[i]);
            Register reg;
            reg.lBits = 0;
            reg.mBits = 0;
            ShorsMainWrapper(factors[i], reg, 0);
        }
    }

    free(factors);
    return 0; // All factors found, end program
}


static int ShorsMainWrapper(int targetNo, Register reg, int aVal){
/*  Performs Shors Algorithm
    Returns 0 if factors are found successfully, 1 otherwise
*/
    int* factors = Xmalloc(2*sizeof(int)); // array of integer factors

    if(targetNo%2 == 0){    // Check if target is even number
        fprintf(stderr, "NOTE: Target number is even!\n");
        factors[0] = 2;
        factors[1] = targetNo/2;
        return FactorSuccess(factors, targetNo);
    }
    
    if(CheckIfPrimeFactor(targetNo)){   // Check if target is a power of lower integer (i.e. targetVal == a^b)
        return 0;
    }

    reg.lBits = CheckRegisterSize(reg.lBits, targetNo*targetNo, 'L'); // Check sizes of registers and sets to optimal if zero
    reg.mBits = CheckRegisterSize(reg.mBits, targetNo, 'M');
    
    if(aVal == 0){ // If invalid a value or not 1st time through
        if(aVal <= 1){
            fprintf(stderr, "WARNING: Invalid 'a' value selected\n");
        }
        Retry:; // If invalid a value chosen return here and try again with different 'a' value
        aVal = 1 + (rand()%(targetNo-1));    // Pick random 'a' value, between 1 and target
    }
    printf("'a' value: %i\n", aVal);

    int gcdVal = Gcd(aVal, targetNo);  // Greatest common demonimator of a and target

    if(gcdVal > 1){     // If GCD is greater than one, GCD is factor of target
        if(aVal == targetNo || aVal == 1){
            goto Retry;
        }
        printf("'a' value creates a factor\n");
        factors[0] = gcdVal;
        factors[1] = targetNo/gcdVal;
        return FactorSuccess(factors, targetNo);
    }
    
    int p = ShorsQuantumPart(targetNo, reg, aVal); // 'Period Finding' part

    // Period checking
    if(p%2 != 0){   // If p odd choose another a value 
        fprintf(stderr, "WARNING: Invalid 'a' value selected (%i), trying again: (period found is odd)\n", aVal);
        goto Retry;
    }
    if(IntPow(aVal, p/2) == -1%targetNo || p == 0){ // if a^(p/2) = -1(mod(target)) choose another a value
        fprintf(stderr, "WARNING: Invalid 'a' value selected (%i), trying again: \n", aVal);
        goto Retry;
    }

    // Factors of targetNo are given by these two expressions
    factors[0] = Gcd(IntPow(aVal, p/2) + 1, targetNo);  
    factors[1] = Gcd(IntPow(aVal, p/2) - 1, targetNo);

    // Factor Checking
    factors = FactorCorrection(factors, targetNo);

    // Check if factors dont multiply to target or trivial factors found
    if(factors[0]*factors[1] != targetNo || (factors[0] == 1 || factors[1] == 1)){ 
        fprintf(stderr, "WARNING: Wrong factors found (%i, %i), trying again\n", factors[0], factors[1]);
        goto Retry;
    }
    else if(factors[0]*factors[1] == targetNo){ // Correct factors found: success
        return FactorSuccess(factors, targetNo);
    }

    free(factors);
    return 1;   // Unknown error
}


int main(int argc, char **argv){
    clock_t startT = clock();
    srand(time(NULL));  // seed rand() function with the time
    
    Register reg;
    reg.lBits = 0; // Can manually change these values to set defaults
    reg.mBits = 0;
    int targetNo = 35;
    int aVal = 31;
    int optionIndex = 0;

     while(1){      // This whole "while" loop is adapted from mat_gen.c
        static struct option long_options[] ={
            {"targetVal", required_argument, 0, 'c'},
            {"mQubits", required_argument, 0, 'm'},
            {"lQubits", required_argument, 0, 'l'},
            {"aVal", required_argument, 0, 'a'},
            {0, 0, 0, 0}
        };
        int choice = getopt_long(argc, argv, "c:m:l:a:", long_options, &optionIndex);
        if (choice == -1) break;
        switch (choice){
            case 'c':
                targetNo = atoi(optarg);
                printf("Target Value: %i\n", targetNo);
                break;
            case 'm':
                reg.mBits = atoi(optarg);
                printf("Number of M Qubits: %i\n", reg.mBits);
                break;
            case 'l':
                reg.lBits = atoi(optarg);
                printf("Number of L Qubits: %i\n", reg.lBits);
                break;
            case 'a':
                aVal = atoi(optarg);
                break;
            default:
                fprintf(stderr, "ERROR: Invalid option\n");
        }
    }
    if (optind < argc) {    // Checks for an invalid argument
        fprintf(stderr,"Invalid Argument: ");
        while (optind < argc) {
            fprintf(stderr, "%s ", argv[optind++]);
        }
        fprintf(stderr, "\n");
    }

    if(targetNo <= 3 || IsPrime(targetNo)){ // Check for valid target number
        fprintf(stderr, "ERROR: Invalid target number (Cannot be prime or less than 4)\n");
        exit(EXIT_FAILURE);
    }

    if(ShorsMainWrapper(targetNo, reg, aVal)){
        fprintf(stderr, "ERROR: Unknown Error\n");
        exit(EXIT_FAILURE);
    }

    printf("Execution Time (s):  %.4lf\n",(double)(clock()-startT)/CLOCKS_PER_SEC);
    return 0;
}