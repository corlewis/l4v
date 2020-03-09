/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int f(int x, int y)
{
  switch (x) {
  case 0:
    x += y;
    break;
  case 1: case 2:
    x -= y * 2;
    return y;
  default:
    x -= y;
  }
  return x;
}


enum {foo = 101,bar};

int g(int y)
{
  int x;
  switch (y) {
  case foo:
    return f(y + 1, 0);
  case bar:
    x = y + 2;
    break;
  default:
    x = 4;
  }
  return x * 2;
}

int h(int z)
{
  switch (z) {
  case foo: case 2: default:
    return 3;
  case bar:
    return 4;
  }
}

int j(int z)
{
  switch (z) {
  case 1: return 3;
  case 2: return 4;
  }
  return 5;
}

int k(int z, int *array)
{
  switch (array[z]) {
  case 0: return 3;
  case 1: return 4;
  default: return 5;
  }
}
