/*
    requires validPointers: valid_read_string(s1) && valid_read_string(s2);
    requires validLengthS1: SIZE_MAX >= strlen(s1) >= 0;
    requires validLengthS2: SIZE_MAX >= strlen(s2) >= 0;
    assigns \nothing ;
    allocates \nothing ;
    frees \nothing ;
    behavior allEqual:
        assumes \forall integer k; 0 <= k <= strlen(s1) ==> s1[k] == s2[k];
        ensures \result == 0;
    behavior SomeDifferent:
        assumes \exists integer k; 0 <= k <= strlen(s1) && s1[k] != s2[k];
        ensures \result != 0;

    disjoint behaviors;
    complete behaviors;
    */
int stringCompare(const char* s1, const char* s2) {
    if (s1 == s2)
        return 0;
    size_t i = 0;
   
    /*@ assert \valid_read(s1) ; */
    /*@ assert \valid_read(s2) ; */
    /*@ loop invariant index: 0 <= i <= strlen(\at(s1,Pre));
        loop invariant index_1: 0 <= i <= strlen(\at(s2,Pre));
        loop invariant s1_pos: s1 == \at(s1,Pre)+i;
        loop invariant s2_pos: s2 == \at(s2,Pre)+i;
        loop invariant equal: \forall integer j; 0 <= j < i ==> \at(s1,Pre)[j] == \at(s2,Pre)[j];
        loop invariant not_eos: \forall integer j; 0 <= j < i ==> \at(s1,Pre)[j] != '\0';
        loop assigns i , s1, s2; */
    while (*s1 == *s2)
    {
        ++i;
        if (*s1 == '\0')
            return 0;
        ++s1;
        ++s2;
    }

    return *s1 - *s2;
}