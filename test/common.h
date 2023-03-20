#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define auto __auto_type

typedef uint64_t u64;
typedef uint32_t u32;
typedef uint16_t u16;
typedef uint8_t u8;
typedef int64_t i64;
typedef int32_t i32;
typedef int16_t i16;
typedef int8_t i8;
typedef float f32;
typedef double f64;
typedef size_t usize;
typedef ssize_t isize;

static inline u16 swap_bytes(const u16 data) {
  return ((data << 8) & 0xff00) | ((data >> 8) & 0x00ff);
}

#define TODO()                                                                 \
  {                                                                            \
    printf("Unimplemented: %s@%s:%d\n", __FUNCTION__, __FILE__, __LINE__);     \
    exit(255);                                                                 \
  }
