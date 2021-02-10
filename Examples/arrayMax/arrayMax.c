#include <stdio.h>
#include <assert.h>
#include <math.h>

int arrayMax(int* arr, int size);

int main(int argc, char** argv){
    int arr[10] = {1,2,3,4,5,6,7,8,9,10};
    arrayMax(arr, 10);
}


int arrayMax(int* arr, int size) {
    __CPROVER_precondition(size > 0, "Precondition: Size positive");
    int result = arr[0];
    int i = 0;

    for(int n=0; n<i; n++){ //Never enters
        __CPROVER_assert(result>=arr[n], "loop invariant: pre");
    }
    while (i < size) {
        for(int n=0; n<i; n++){
        __CPROVER_assert(result>=arr[n], "loop invariant: at");
        }
        if (arr[i] > result) 
            result = arr[i];

        i++;
    }
    for(int n=0; n<i; n++){
        __CPROVER_assert(result>=arr[n], "loop invariant: post");
    }

    //Postcondition Start
    int exists = 0;
    for(int n = 0; n < size; n++){
        if(arr[n] == result)
            exists = 1;
        __CPROVER_assert(result >= arr[n], "Postcondition: Result greater than"); 
    }
    __CPROVER_assert(exists==1, "Postcondition: Result exists in array"); 
    //Postcondition End

    return result;
}

//cbmc arrayMax.c --bounds-check --pointer-check 


/*
Ting der ikke tjekkes, i.f.t. frama-c:
    \assigns nothing

    
/Reflections
    Giver loop invarianter overhovedet mening?
/*