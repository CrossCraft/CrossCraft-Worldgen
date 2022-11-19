#include <stdint.h>
#include <stdbool.h>
#include <limits.h>
typedef uint64_t rep_t;
typedef int64_t srep_t;
typedef double fp_t;
#define REP_C UINT64_C
#define significandBits 52

#define typeWidth       (sizeof(rep_t)*CHAR_BIT)
#define exponentBits    (typeWidth - significandBits - 1)
#define maxExponent     ((1 << exponentBits) - 1)
#define exponentBias    (maxExponent >> 1)

#define implicitBit     (REP_C(1) << significandBits)
#define significandMask (implicitBit - 1U)
#define signBit         (REP_C(1) << (significandBits + exponentBits))
#define absMask         (signBit - 1U)
#define exponentMask    (absMask ^ significandMask)
#define oneRep          ((rep_t)exponentBias << significandBits)
#define infRep          exponentMask
#define quietBit        (implicitBit >> 1)
#define qnanRep         (exponentMask | quietBit)

static __inline rep_t toRep(fp_t x) {
  const union {
    fp_t f;
    rep_t i;
  } rep = {.f = x};
  return rep.i;
}

static __inline fp_t fromRep(rep_t x) {
  const union {
    fp_t f;
    rep_t i;
  } rep = {.i = x};
  return rep.f;
}


fp_t __floatsisf(int a) {
    
    const int aWidth = sizeof a * CHAR_BIT;
    
    // Handle zero as a special case to protect clz
    if (a == 0)
        return fromRep(0);
    
    // All other cases begin by extracting the sign and absolute value of a
    rep_t sign = 0;
    if (a < 0) {
        sign = signBit;
        a = -a;
    }
    
    // Exponent of (fp_t)a is the width of abs(a).
    const int exponent = (aWidth - 1) - __builtin_clz(a);
    rep_t result;
    
    // Shift a into the significand field, rounding if it is a right-shift
    if (exponent <= significandBits) {
        const int shift = significandBits - exponent;
        result = (rep_t)a << shift ^ implicitBit;
    } else {
        const int shift = exponent - significandBits;
        result = (rep_t)a >> shift ^ implicitBit;
        rep_t round = (rep_t)a << (typeWidth - shift);
        if (round > signBit) result++;
        if (round == signBit) result += result & 1;
    }
    
    // Insert the exponent
    result += (rep_t)(exponent + exponentBias) << significandBits;
    // Insert the sign bit and return
    return fromRep(result | sign);
}

fp_t __floatunsisf(unsigned int a) {

  const int aWidth = sizeof a * CHAR_BIT;

  // Handle zero as a special case to protect clz
  if (a == 0)
    return fromRep(0);

  // Exponent of (fp_t)a is the width of abs(a).
  const int exponent = (aWidth - 1) - __builtin_clz(a);
  rep_t result;

  // Shift a into the significand field, rounding if it is a right-shift
  if (exponent <= significandBits) {
    const int shift = significandBits - exponent;
    result = (rep_t)a << shift ^ implicitBit;
  } else {
    const int shift = exponent - significandBits;
    result = (rep_t)a >> shift ^ implicitBit;
    rep_t round = (rep_t)a << (typeWidth - shift);
    if (round > signBit)
      result++;
    if (round == signBit)
      result += result & 1;
  }

  // Insert the exponent
  result += (rep_t)(exponent + exponentBias) << significandBits;
  return fromRep(result);
}
typedef int si_int;
typedef unsigned su_int;
typedef si_int fixint_t;
typedef su_int fixuint_t;

static __inline fixuint_t __fixuint(fp_t a) {
  // Break a into sign, exponent, significand parts.
  const rep_t aRep = toRep(a);
  const rep_t aAbs = aRep & absMask;
  const int sign = aRep & signBit ? -1 : 1;
  const int exponent = (aAbs >> significandBits) - exponentBias;
  const rep_t significand = (aAbs & significandMask) | implicitBit;

  // If either the value or the exponent is negative, the result is zero.
  if (sign == -1 || exponent < 0)
    return 0;

  // If the value is too large for the integer type, saturate.
  if ((unsigned)exponent >= sizeof(fixuint_t) * CHAR_BIT)
    return ~(fixuint_t)0;

  // If 0 <= exponent < significandBits, right shift to get the result.
  // Otherwise, shift left.
  if (exponent < significandBits)
    return significand >> (significandBits - exponent);
  else
    return (fixuint_t)significand << (exponent - significandBits);
}

static __inline fixint_t __fixint(fp_t a) {
  const fixint_t fixint_max = (fixint_t)((~(fixuint_t)0) / 2);
  const fixint_t fixint_min = -fixint_max - 1;
  // Break a into sign, exponent, significand parts.
  const rep_t aRep = toRep(a);
  const rep_t aAbs = aRep & absMask;
  const fixint_t sign = aRep & signBit ? -1 : 1;
  const int exponent = (aAbs >> significandBits) - exponentBias;
  const rep_t significand = (aAbs & significandMask) | implicitBit;

  // If exponent is negative, the result is zero.
  if (exponent < 0)
    return 0;

  // If the value is too large for the integer type, saturate.
  if ((unsigned)exponent >= sizeof(fixint_t) * CHAR_BIT)
    return sign == 1 ? fixint_max : fixint_min;

  // If 0 <= exponent < significandBits, right shift to get the result.
  // Otherwise, shift left.
  if (exponent < significandBits)
    return sign * (significand >> (significandBits - exponent));
  else
    return sign * ((fixint_t)significand << (exponent - significandBits));
}

fp_t __floatsidf(int a) {

  const int aWidth = sizeof a * CHAR_BIT;

  // Handle zero as a special case to protect clz
  if (a == 0)
    return fromRep(0);

  // All other cases begin by extracting the sign and absolute value of a
  rep_t sign = 0;
  if (a < 0) {
    sign = signBit;
    a = -a;
  }

  // Exponent of (fp_t)a is the width of abs(a).
  const int exponent = (aWidth - 1) - __builtin_clz(a);
  rep_t result;

  // Shift a into the significand field and clear the implicit bit.  Extra
  // cast to unsigned int is necessary to get the correct behavior for
  // the input INT_MIN.
  const int shift = significandBits - exponent;
  result = (rep_t)(unsigned int)a << shift ^ implicitBit;

  // Insert the exponent
  result += (rep_t)(exponent + exponentBias) << significandBits;
  // Insert the sign bit and return
  return fromRep(result | sign);
}

fp_t __floatunsidf(unsigned int a) {

  const int aWidth = sizeof a * CHAR_BIT;

  // Handle zero as a special case to protect clz
  if (a == 0)
    return fromRep(0);

  // Exponent of (fp_t)a is the width of abs(a).
  const int exponent = (aWidth - 1) - __builtin_clz(a);
  rep_t result;

  // Shift a into the significand field and clear the implicit bit.
  const int shift = significandBits - exponent;
  result = (rep_t)a << shift ^ implicitBit;

  // Insert the exponent
  result += (rep_t)(exponent + exponentBias) << significandBits;
  return fromRep(result);
}
#define SRC_REP_C UINT64_C

typedef double src_t;
typedef uint64_t src_rep_t;
typedef double dst_t;
typedef uint64_t dst_rep_t;
static const int srcSigBits = 52;

static const int dstSigBits = 52;

static __inline int src_rep_t_clz(src_rep_t a) {
  return __builtin_clzl(a);
}

static __inline src_rep_t srcToRep(src_t x) {
  const union {
    src_t f;
    src_rep_t i;
  } rep = {.f = x};
  return rep.i;
}

static __inline dst_t dstFromRep(dst_rep_t x) {
  const union {
    dst_t f;
    dst_rep_t i;
  } rep = {.i = x};
  return rep.f;
}

#define DST_REP_C UINT64_C

static __inline dst_t __extendXfYf2__(src_t a) {
  // Various constants whose values follow from the type parameters.
  // Any reasonable optimizer will fold and propagate all of these.
  const int srcBits = sizeof(src_t) * CHAR_BIT;
  const int srcExpBits = srcBits - srcSigBits - 1;
  const int srcInfExp = (1 << srcExpBits) - 1;
  const int srcExpBias = srcInfExp >> 1;

  const src_rep_t srcMinNormal = SRC_REP_C(1) << srcSigBits;
  const src_rep_t srcInfinity = (src_rep_t)srcInfExp << srcSigBits;
  const src_rep_t srcSignMask = SRC_REP_C(1) << (srcSigBits + srcExpBits);
  const src_rep_t srcAbsMask = srcSignMask - 1;
  const src_rep_t srcQNaN = SRC_REP_C(1) << (srcSigBits - 1);
  const src_rep_t srcNaNCode = srcQNaN - 1;

  const int dstBits = sizeof(dst_t) * CHAR_BIT;
  const int dstExpBits = dstBits - dstSigBits - 1;
  const int dstInfExp = (1 << dstExpBits) - 1;
  const int dstExpBias = dstInfExp >> 1;

  const dst_rep_t dstMinNormal = DST_REP_C(1) << dstSigBits;

  // Break a into a sign and representation of the absolute value.
  const src_rep_t aRep = srcToRep(a);
  const src_rep_t aAbs = aRep & srcAbsMask;
  const src_rep_t sign = aRep & srcSignMask;
  dst_rep_t absResult;

  // If sizeof(src_rep_t) < sizeof(int), the subtraction result is promoted
  // to (signed) int.  To avoid that, explicitly cast to src_rep_t.
  if ((src_rep_t)(aAbs - srcMinNormal) < srcInfinity - srcMinNormal) {
    // a is a normal number.
    // Extend to the destination type by shifting the significand and
    // exponent into the proper position and rebiasing the exponent.
    absResult = (dst_rep_t)aAbs << (dstSigBits - srcSigBits);
    absResult += (dst_rep_t)(dstExpBias - srcExpBias) << dstSigBits;
  }

  else if (aAbs >= srcInfinity) {
    // a is NaN or infinity.
    // Conjure the result by beginning with infinity, then setting the qNaN
    // bit (if needed) and right-aligning the rest of the trailing NaN
    // payload field.
    absResult = (dst_rep_t)dstInfExp << dstSigBits;
    absResult |= (dst_rep_t)(aAbs & srcQNaN) << (dstSigBits - srcSigBits);
    absResult |= (dst_rep_t)(aAbs & srcNaNCode) << (dstSigBits - srcSigBits);
  }

  else if (aAbs) {
    // a is denormal.
    // renormalize the significand and clear the leading bit, then insert
    // the correct adjusted exponent in the destination type.
    const int scale = src_rep_t_clz(aAbs) - src_rep_t_clz(srcMinNormal);
    absResult = (dst_rep_t)aAbs << (dstSigBits - srcSigBits + scale);
    absResult ^= dstMinNormal;
    const int resultExponent = dstExpBias - srcExpBias - scale + 1;
    absResult |= (dst_rep_t)resultExponent << dstSigBits;
  }

  else {
    // a is zero.
    absResult = 0;
  }

  // Apply the signbit to the absolute value.
  const dst_rep_t result = absResult | (dst_rep_t)sign << (dstBits - srcBits);
  return dstFromRep(result);
}

si_int __fixsfsi(fp_t a) { return __fixint(a); }
su_int __fixunssfsi(fp_t a) { return __fixuint(a); }
si_int __fixdfsi(fp_t a) { return __fixint(a); }
double __extendsfdf2(float a) { return __extendXfYf2__(a); }