/* Time budgets across translation units (scripts/crosscheck_link.py, with
   time_budget_main.c): the loop of sum_row is bounded from this file's report, the loop of
   its callers from the other one; the binary is the linked program. */
int grid[16][16];
int sum_row(int i) {
  int s = 0;
  for (int j = 0; j < 16; j++) s += grid[i & 15][j];
  return s;
}
