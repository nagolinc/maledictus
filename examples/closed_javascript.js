/**
 * @param {number} value
 * @returns {number}
 */
function shifted(value) {
  return value + 2;
}

/**
 * @param {boolean} flag
 * @param {number} left
 * @param {number} right
 * @returns {number}
 */
export function choose(flag, left, right) {
  if (flag) {
    const selected = shifted(left);
    return selected;
  }
  return shifted(right);
}
