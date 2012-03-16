/* Copyright (C) 2012 Free Software Foundation, Inc.
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




#define _GNU_SOURCE

#ifdef HAVE_CONFIG_H
#  include <config.h>
#endif

#include "libguile/_scm.h"
#include "libguile/bytevectors.h"
#include "libguile/error.h"
#include "libguile/numbers.h"
#include "libguile/socket.h"
#include "libguile/validate.h"

#include "libguile/nio.h"

#ifdef HAVE_WINSOCK2_H
#include <winsock2.h>
#else
#include <sys/socket.h>
#ifdef HAVE_UNIX_DOMAIN_SOCKETS
#include <sys/un.h>
#endif
#include <netinet/in.h>
#include <netdb.h>
#include <arpa/inet.h>
#endif



/* {Non-blocking I/O}
 */

/* Read COUNT bytes from FD into BV, and write them at POS.  Return the
   number of bytes read, or -1 if no bytes could be read without
   blocking.  A return value of 0 indicates EOF.
 */
static SCM
scm_nio_read (SCM fd, SCM bv, SCM pos, SCM count)
#define FUNC_NAME "nio-read"
{
  int c_fd;
  ssize_t rv;
  signed char *data;
  size_t c_pos, c_count;
  int try_again;

  c_fd = scm_to_int (fd);
  SCM_VALIDATE_BYTEVECTOR (SCM_ARG2, bv);
  data = SCM_BYTEVECTOR_CONTENTS (bv);
  c_pos = scm_to_size_t (pos);
  c_count = scm_to_size_t (count);
  
  if (SCM_UNLIKELY (SCM_BYTEVECTOR_LENGTH (bv) < c_pos))
    SCM_OUT_OF_RANGE (SCM_ARG3, pos);
  if (SCM_UNLIKELY (c_count > SCM_BYTEVECTOR_LENGTH (bv) - c_pos))
    SCM_OUT_OF_RANGE (SCM_ARG4, count);

  data += c_pos;

  rv = read (c_fd, data, c_count);
  try_again = (errno == EWOULDBLOCK || errno == EAGAIN);

  if (rv < 0 && !try_again)
    SCM_SYSERROR;
  if (rv <= 0 && try_again)
    return scm_from_ssize_t (-1);
  else
    return scm_from_ssize_t (rv);
}
#undef FUNC_NAME

/* Write to FD the COUNT bytes from BV starting at POS.  Return the
   number of bytes written, which may be less than COUNT if a write would
   block.
 */
static SCM
scm_nio_write (SCM fd, SCM bv, SCM pos, SCM count)
#define FUNC_NAME "nio-write"
{
  int c_fd;
  ssize_t rv;
  signed char *data;
  size_t c_pos, c_count;
  int try_again;

  c_fd = scm_to_int (fd);
  SCM_VALIDATE_BYTEVECTOR (SCM_ARG2, bv);
  data = SCM_BYTEVECTOR_CONTENTS (bv);
  c_pos = scm_to_size_t (pos);
  c_count = scm_to_size_t (count);
  
  if (SCM_UNLIKELY (SCM_BYTEVECTOR_LENGTH (bv) < c_pos))
    SCM_OUT_OF_RANGE (SCM_ARG3, pos);
  if (SCM_UNLIKELY (c_count > SCM_BYTEVECTOR_LENGTH (bv) - c_pos))
    SCM_OUT_OF_RANGE (SCM_ARG4, count);

  data += c_pos;

  rv = write (c_fd, data, c_count);
  try_again = (errno == EWOULDBLOCK || errno == EAGAIN);

  if (rv < 0 && !try_again)
    SCM_SYSERROR;

  return scm_from_ssize_t ((rv < 0) ? 0 : rv);
}
#undef FUNC_NAME

/* The largest possible socket address.  Wrapping it in a union guarantees
   that the compiler will make it suitably aligned.  */
typedef union
{
  struct sockaddr     sockaddr;
  struct sockaddr_in  sockaddr_in;

#ifdef HAVE_UNIX_DOMAIN_SOCKETS
  struct sockaddr_un  sockaddr_un;
#endif
#ifdef HAVE_IPV6
  struct sockaddr_in6 sockaddr_in6;
#endif
} scm_t_max_sockaddr;

/* Like @code{accept}, but instead of returning a pair whose
   @emph{car} is a port, returns a pair whose @emph{car} is a
   file descriptor.  Also, if the @code{accept} call failed with
   @code{EAGAIN} or @code{EWOULDBLOCK}, returns @code{#f} instead
   of throwing an exception. */
static SCM
scm_nio_accept (SCM fd)
#define FUNC_NAME "nio-accept"
{
  int c_fd;
  int newfd;
  socklen_t addr_size = sizeof (scm_t_max_sockaddr);
  scm_t_max_sockaddr addr;

  c_fd = scm_to_int (fd);
  newfd = accept (c_fd, (struct sockaddr *) &addr, &addr_size);

  if (newfd >= 0)
    return scm_cons (scm_from_int (newfd),
                     scm_from_sockaddr ((struct sockaddr *) &addr, addr_size));
  else if (errno == EAGAIN || errno == EWOULDBLOCK)
    return SCM_BOOL_F;
  else
    SCM_SYSERROR;
}
#undef FUNC_NAME




/* Low-level helpers for (ice-9 nio).  */
static void
scm_init_nio (void)
{
  scm_c_define_gsubr ("%nio-read", 4, 0, 0, scm_nio_read);
  scm_c_define_gsubr ("%nio-write", 4, 0, 0, scm_nio_write);
  scm_c_define_gsubr ("%nio-accept", 1, 0, 0, scm_nio_accept);
}

void
scm_register_nio (void)
{
  scm_c_register_extension ("libguile-" SCM_EFFECTIVE_VERSION,
                            "scm_init_nio",
			    (scm_t_extension_init_func) scm_init_nio,
			    NULL);
}

/*
  Local Variables:
  c-file-style: "gnu"
  End:
*/
