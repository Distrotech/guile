/* classes: h_files */

#ifndef SCM_DEBUG_H
#define SCM_DEBUG_H

/* Copyright (C) 1995,1996,1998,1999,2000,2001,2002,2004,2008,2009,2010,2011,2012,2013
 * Free Software Foundation, Inc.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 */



#include "libguile/__scm.h"

#include "libguile/options.h"


/* {Evaluator}
 */

typedef union scm_t_debug_info
{
  struct { SCM exp, env; } e;
  struct { SCM proc, args; } a;
  SCM id;
} scm_t_debug_info;



SCM_API SCM scm_local_eval (SCM exp, SCM env);

SCM_API SCM scm_reverse_lookup (SCM env, SCM data);
SCM_API SCM scm_debug_options (SCM setting);

SCM_INTERNAL void scm_init_debug (void);

#ifdef GUILE_DEBUG
SCM_API SCM scm_debug_hang (SCM obj);
#endif /*GUILE_DEBUG*/

#endif  /* SCM_DEBUG_H */

/*
  Local Variables:
  c-file-style: "gnu"
  End:
*/
