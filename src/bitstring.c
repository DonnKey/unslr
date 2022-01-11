#include <memory.h>
#include <assert.h>

#include "type.h"
#include "bitstring.h"
/*             **************************************
               *                                    *
               *      bit string manipulation       *
               *             routines               *
               *                                    *
               **************************************
*/
/*
   all functions but x_not work as expected.  x_not assumes
   that the length specifies the universe, and thus a dummy
   set or reset must be used to guarantee that the last bit
   in the universe is in fact defined.
*/

/*
NOTE: the C implementation hews very closely to the XPL/S, and consequently
probably leaks (XPL garbage collected strings).  Not worth the effort for
an inherently short-lived program such as this, although if rewriting in a
modern language, it would be easy enough to fix.
*/

char *hexbits(bitstring str)
/*  dump a bit string in hex  */
{
   int i;
   static char str2[220];
   int len;

   if (str == NULLBITS) return "NULLBITS";
   if (str->maxIndex == -1) {
        return "EMPTY";
   }
   if (str->maxIndex < -1) {
        return "ILLFORMED";
   }
   len = (str->maxIndex+8)/8;
   int p = 0;
   for (i=0 ; i < len && i < 200/2; i++) {
        p += sprintf(&str2[2*i],"%2.2x",str->bits[i]&0xff);
   }
   sprintf(&str2[p], " (%d)", str->maxIndex);
   return str2;
}

static bitstring x_bitstring(bitstring str)
{
   int len;
   if (str == NULLBITS) {
       str = (bitstring)malloc(sizeof(struct bitstring));
       str->maxIndex = -1;
       str->bits[0] = 0;
   }
   return str;
}

void x_set(bitstring *str, int bitindex)
/*  set a single bit   */
{
   int i;
   *str = x_bitstring(*str);
   if (bitindex < 0) return;
   if ((bitindex+8)/8 > ((*str)->maxIndex+8)/8) {
      *str = (bitstring) realloc(*str,sizeof(struct bitstring) + (bitindex+8)/8);
      for (i=((*str)->maxIndex+8)/8+1;i <= (bitindex+8)/8; i++) (*str)->bits[i]=0;
   }
   if ((*str)->maxIndex < bitindex) (*str)->maxIndex = bitindex;
   (*str)->bits[bitindex/8] |= 0x80>>bitindex%8;
   assert((*str)->maxIndex >= 0);
}

void x_reset(bitstring *str, int bitindex)
/*  clear a single bit  */
{
   int i;

   *str = x_bitstring(*str);
   if (bitindex < 0) return;
   if ((bitindex+8)/8 > ((*str)->maxIndex+8)/8) {
      *str = (bitstring) realloc(*str,sizeof(struct bitstring) + (bitindex+8)/8);
      for (i=((*str)->maxIndex+8)/8+1; i <= (bitindex+8)/8; i++) (*str)->bits[i]=0;
   }
   if ((*str)->maxIndex < bitindex) (*str)->maxIndex = bitindex;
   (*str)->bits[bitindex/8] &= ~(0x80>>bitindex%8);
   assert((*str)->maxIndex >= 0);
}

boolean x_test(bitstring str, int bitindex)
/*  return value of a single bit  */
{
   if (str == NULLBITS) return false;
   if (bitindex < 0) return false;
   if (bitindex > str->maxIndex) return false;
   return (str->bits[bitindex/8] & (0x80>>(bitindex%8))) != 0;
}

void x_and(bitstring *str0, bitstring str1, bitstring str2)
/* the logical product of two bit strings */
{
   bitstring str3;
   bitstring res;
   int i,len;

   res = x_bitstring(NULLBITS);
   str1 = x_bitstring(str1);
   str2 = x_bitstring(str2);
   if (str2->maxIndex > str1->maxIndex) {
      str3 = str1;
      str1 = str2;
      str2 = str3;
   }
   /*  str1 is now the longer; the result will be truncated to the length
       of str2 */
   len = (str2->maxIndex+8)/8;
   res = (bitstring) realloc(res, sizeof(struct bitstring)+len);
   res->maxIndex = str2->maxIndex;

   for (i = 0; i<len-1; i++) {
      res->bits[i] = str2->bits[i] & str1->bits[i];
   }
   res->bits[len-1] = str2->bits[len-1] & str1->bits[len-1] &
               ~(0x7f >> (str2->maxIndex%8));
   assert(res->maxIndex >= 0);
   *str0 = res;
}

void x_or(bitstring *str0, bitstring str1, bitstring str2)
/* the logical sum of two bit strings; will be the length of the longer  */
{
   bitstring str3;
   int i,len;
   bitstring res;

   res = x_bitstring(NULLBITS);
   str1 = x_bitstring(str1);
   str2 = x_bitstring(str2);
   if (str2->maxIndex > str1->maxIndex) {
      str3 = str1;
      str1 = str2;
      str2 = str3;
   }
   /* str1 is now the longer; the result will be that of str1 */
   len = (str1->maxIndex+8)/8;
   res = (bitstring) realloc(res, sizeof(struct bitstring)+len);
   res->maxIndex = str1->maxIndex;

   /* combine the common prefix */
   len = (str2->maxIndex+8)/8;
   for (i = 0; i<len; i++) {
      res->bits[i] = str1->bits[i] | str2->bits[i];
   }

   /* just copy the remainder; clip the last byte */
   len = (str1->maxIndex+8)/8;
   for (; i<len; i++) {
      res->bits[i] = str1->bits[i];
   }
   res->bits[len] &= ~(0x7f >> (res->maxIndex%8));
   assert(res->maxIndex >= 0);
   *str0 = res;
}

void x_not(bitstring *str0, bitstring str1)
/*  inverse of a bit string up to the last defined bit  */
{
   int i,len;
   bitstring res;

   res = x_bitstring(NULLBITS);
   str1 = x_bitstring(str1);
   len = (str1->maxIndex+8)/8;
   res = (bitstring)realloc(*str0, sizeof(struct bitstring)+len);
   res->maxIndex = str1->maxIndex;

   for (i=0; i<len; i++) {
      res->bits[i] = ~str1->bits[i];
   }
   res->bits[len-1] &= ~(0x7f>>(str1->maxIndex%8));
   assert(res->maxIndex >= 0);
   *str0 = res;
}

boolean x_equal(bitstring str1, bitstring str2)
{
   bitstring str3;
   int i,len1,len2,bits2;

   if (str1->maxIndex == -1 && str2->maxIndex == -1) return true;
   str1 = x_bitstring(str1);
   str2 = x_bitstring(str2);
   if (str2->maxIndex > str1->maxIndex) {
      str3 = str1;
      str1 = str2;
      str2 = str3;
   }

   /*  str1 is now the longer */

   len1 = (str1->maxIndex+8)/8 - 1;
   if (str2->maxIndex != -1) {
      len2 = (str2->maxIndex+8)/8 - 1;

      /* compare common prefix*/
      for (i = 0; i<len2; i++) {
         if (str2->bits[i] != str1->bits[i]) return false;
      }

      /* compare trailing partial byte */
      if ((str1->bits[len2] & ~(0x7f >> (str2->maxIndex%8))) !=
          (str2->bits[len2] & ~(0x7f >> (str2->maxIndex%8)))) return false;
      bits2 = str2->maxIndex%8+1;
   }
   else {
      len2 = 0;
      bits2 = 0;
   }

   if (str1->maxIndex == str2->maxIndex) return true;

   /* if lengths differ all trailing bits must be zero */
   if (len1 > len2) {
           /* all of one chunk, plus maybe more, and a trailing part. */
           if ((str1->bits[len2] & (0xff >> bits2)) != 0) return 0;

           /* then whole bytes */
           for (i = len2+1; i<len1; i++) {
              if (str1->bits[i] != 0) return 0;
           }
           /* and the partial chunk */
           if ((str1->bits[len1] & ~(0x7f >> (str1->maxIndex%8))) != 0) return false;
   }
   else {
        /* a few more bits in one chunk */
           if ((str1->bits[len2] & (0xff >> bits2)
                                 & ~(0x7f >> (str1->maxIndex%8))) != 0) return false;
   }
   return 1;
}

void x_minus(bitstring *str0, bitstring str1, bitstring str2)
{
   bitstring str3;
   str1 = x_bitstring(str1);

   str3 = newbits(str2);
   if (str3->maxIndex < str1->maxIndex) {
      x_reset(&str3, str1->maxIndex);
   }
   x_not(&str3, str3);
   x_and(str0, str1, str3);

   freebits(&str3);
}

int x_count(bitstring str)
/*  count number of elements (ones)  */
{
   int i, j, count;
   char item;
   int len;

   str = x_bitstring(str);
   len = str->maxIndex;
   if (len == -1) return 0;
   len = (len+8)/8 - 1;
   count = 0;
   for (i=0; i<len; i++) {
      item = str->bits[i];
      if (item != 0) {
         for (j=0; j<8; j++) {
            if (((item >> j) & 1) != 0) count = count + 1;
         }
      }
   }
   item = str->bits[len] & ~(0x7f>>(str->maxIndex%8));

   if (item != 0) {
      for (j=0; j<8; j++) {
         if (((item >> j) & 1) != 0) count = count + 1;
      }
   }
   return count;
}

boolean x_empty(bitstring str)
/*  test for empty set  */
{
   int i,len;

   if (str == NULLBITS) return true;
   if (str->maxIndex == -1) return true;
   str = x_bitstring(str);
   len = (str->maxIndex+8)/8;

   for (i=0 ; i<len-1; i++) {
      if (str->bits[i] != 0) return false;
   }
   i = str->bits[len-1] & ~(0x7f >> (str->maxIndex%8)) & 0xff;
   return (i == 0);
}

bitstring newbits(bitstring str)
{
        bitstring s;
        if (str == NULLBITS) {
           return NULLBITS;
        }

        s = (bitstring) malloc(sizeof(struct bitstring)+(str->maxIndex+8)/8);
        memcpy(s,str,sizeof(struct bitstring)+(str->maxIndex+8)/8);
        return s;
}

void freebits(bitstring *s)
{
        if (*s != NULLBITS) free(*s);
        *s = NULLBITS;
}

void x_setempty(bitstring *str)
{
        freebits(str);
        *str=x_bitstring(NULLBITS);
}

boolean x_empty_minus(bitstring str1, bitstring str2)
{
        bitstring str;
        boolean foo;

        str=NULLBITS;
        x_minus(&str, str1, str2);
        foo = x_empty(str);
        freebits(&str);
        return foo;
}


boolean x_empty_and(bitstring str1, bitstring str2)
{
        bitstring str;
        boolean foo;

        str=NULLBITS;
        x_and(&str, str1, str2);
        foo = x_empty(str);
        freebits(&str);
        return foo;
}
