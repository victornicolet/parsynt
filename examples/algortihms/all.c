#include "stdio.h"

#define max(a,b) ((a>b)? a : b)
/*
  Examples from "Automatic Inversion Generates Divide and Conquer Parallel
  Programs"
  MPS, MSS, Line-of-sight
*/

// Maximum prefix sum

float maximum_prefix_sum (float* a, size_t n) {
  int i;
  float mps = a[0], sum = 0;
  for (i = 0; i < n; i++) {
    sum += a[i];
    mps = max(mps, sum);
  }
  return mps;
}


// Line of sight
int visible (float *a, size_t n) {
  int i;
  float amax = 0;
  int visible = 1;
  for (i = 0; i < n; i++) {
    visible = (amax <= a[i])?1:0;
    amax = max(amax, a[i]);
  }
  return visible;
}

// Maximum segment sum
float maximum_segment_sum(float *a, size_t n) {
  int i;
  float mps = 0, mss = 0, mps = 0, sum = 0;
  for (i = 0; i < n; i ++) {
    mss = max(mss, mts + a[i]);
    mps = max(mps, sum + a[i]);
    mts = max(mts + a[i], 0);
    sum = sum + a[i];
  }
  return mss;
}

/* 
   Other examples sorted by complexity (for the concurrent solution)
*/
float second_largest_element (float *a, size_t n) {
  float max = 0, smax = 0;
  int i = 0;
  for (i = 0; i < n; i++) {
    if (a[i] > max) { max = a[i]; smax = max; }
    else if (a[i] > smax) smax = a[i];
  }
  return smax;
}

float majority (float *a, size_t n) {
  int c = 1, i = 0;
  float m = a[0];
  for (i = 1; i < n; i++) {
    if (c == 0) {
      m = a[i];
      c = 1;
    } else if (a[i] == m) {
      c++;
    } else {
      c--;
    }
  }
  return m;
}

// Boyer-Moor-Horspool substring searching
int *preprocess (char *word, int word_len) {
  int t[256];
  int i;
  for (i = 0; i < 256; i++) {
    t[i] = word_len;
  }
  for(i = 0; i < word_len - 1; i++) {
    t[word[i]] = word_len - 1 - i;
  }
  return t;
}

int search(char *word, char *text, int word_len, int text_len) {
  int *t = preprocess (word, word_len);
  int skip = 0;
  int i;
  while (text_len - skip >= word_len) {
    i = word_len - 1;
    while (text[skip + i] == word[i]) {
      if (i == 0) return skip;
      i --;
    }
    skip += t[text[skip + word_len - 1]];
  }
  return -1;
}

