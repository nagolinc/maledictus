function shifted(value: number): number {
  return value + 2;
}

export function choose(flag: boolean, left: number, right: number): number {
  if (flag) {
    const selected = shifted(left);
    return selected;
  }
  return shifted(right);
}
