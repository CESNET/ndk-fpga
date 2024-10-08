/**
 * \file frl_spdconv.c
 * \author Jakub Lukac <xlukac09@stud.fit.vutbr.cz>
 * \date 2015-09
 *
 * Copyright (C) 2015 CESNET
 */

#include "frl.h"

/**
 * \brief Convert speed limit [kBps] to item parts speed and t_const
 *        Wrapper function for rational approximation
 * \param s         Speed limit [kBps], positive integer or zero
 * \param max_s     Maximal speed value
 * \param max_t_c   Maximal time constant value
 * \param r_speed   Reference to an int type, whose value is set by the function
 * \param r_t_const Reference to an int type, whose value is set by the function
 * \retval zero Exact conversion
 * \retval one  Best approximation of speed \a s
 *
 * \note
 * SPEED value is returned as *r_speed and TIME_CONST value is returned as *r_t_const
 */
int frl_spdconv(uint32_t s, uint32_t max_s, uint32_t max_t_c, uint32_t *r_speed, uint32_t *r_t_const)
{
   return rat((double)s/1000000, max_t_c, max_s, r_t_const, r_speed);
}

/**
 * \brief Rational approximation with numerator and denominator below a given limit
 *        (farey approximation)
 * \param x         Value which be converted to fraction
 * \param max_num   Maximal value of numerator (this not included)
 * \param max_denom Maximal value of denominator (this not included)
 * \param r_num     Reference to an int type, whose value is set by the function
 * \param r_denom   Reference to an int type, whose value is set by the function
 * \retval zero Exact conversion
 * \retval one  Best approximation of \a x
 *
 * \note
 * Function always return irreducible fraction parts
 */
int rat(double x, uint32_t max_num, uint32_t max_denom, uint32_t *r_num, uint32_t *r_denom)
{
   uint32_t a, b, c, d;
   a = floor(x);     b = 1;
   c = floor(x) + 1; d = 1;

   double mediant;
   while (a < max_num &&
          c < max_num &&
          b < max_denom &&
          d < max_denom) {
      mediant = (double)(a+c)/(b+d);

      if (x == mediant) {
         if (a+c < max_num && b+d < max_denom) {
            *r_num = a+c;
            *r_denom = b+d;
            return 0;
         }
         else {
            *r_num   = b > d ? a : c;
            *r_denom = b > d ? b : d;
            return 1;
         }
      }
      else if (x > mediant) {
         *r_num = a;
         *r_denom = b;
         a = a+c;
         b = b+d;
      }
      else {
         *r_num = c;
         *r_denom = d;
         c = a+c;
         d = b+d;
      }
   }  // end while

   if (a < max_num && b < max_denom) {
      if (fabs((double)a/b - x) < fabs((double)*r_num/ *r_denom - x)) {
         *r_num   = a;
         *r_denom = b;
      }
   }
   else {
      if (fabs((double)c/d - x) < fabs((double)*r_num/ *r_denom - x)) {
         *r_num   = c;
         *r_denom = d;
      }
   }
   return 1;
}
