#include "structs.h"

#define T int
#define TArray_IMPLEMENT
#include "macro-array.h"
#undef T

#define T LocalData
#define TArray_IMPLEMENT
#include "macro-array.h"
#undef T
