/* Copyright (C) 2010, 2012 Free Software Foundation, Inc.
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
#include "libguile/numbers.h"
#include "libguile/error.h"
#include "libguile/validate.h"

#include "libguile/poll.h"


#ifdef HAVE_POLL_H
#include <poll.h>
#endif

#ifdef HAVE_SYS_EPOLL_H
#include <sys/epoll.h>
#define HAVE_EPOLL
#endif



/* {Poll}
 */

/* Poll a set of file descriptors, waiting until one or more of them is
   ready to perform input or output.

   This is a low-level interface.  See the `(ice-9 poll)' module for a more
   usable wrapper.

   `pollfds' is expected to be a bytevector, laid out in contiguous blocks of 64
   bits.  Each block has the format of one `struct pollfd': a 32-bit int file
   descriptor, a 16-bit int events mask, and a 16-bit int revents mask.

   The number of pollfd structures in `pollfds' is specified in
   `nfds'. `pollfds' must be at least long enough to support that number of
   structures. It may be longer, in which case the trailing entries are left
   untouched.

   The pollfds bytevector is modified directly, setting the returned events in
   the final two bytes (the revents member).

   Since Scheme ports can buffer input or output in userspace, a Scheme
   poll interface needs to take that into account as well.  The `ports'
   argument, a vector big enough for `nfds' elements, is given for this
   purpose.  If a pollfd entry has a corresponding open port, that port
   is scanned for available input or output before dropping into the
   poll.  If any port has buffered I/O available, the poll syscall is
   still issued, but with a timeout of 0 milliseconds, and a full port
   scan occurs after the poll returns.

   If timeout is given and is non-negative, the poll will return after that
   number of milliseconds if no fd became active.
   */
#ifdef HAVE_POLL
static SCM
scm_primitive_poll (SCM pollfds, SCM nfds, SCM ports, SCM timeout)
#define FUNC_NAME "primitive-poll"
{
  int rv = 0;
  nfds_t i;
  nfds_t c_nfds;
  int c_timeout;
  int have_buffered_io = 0;
  struct pollfd *fds;

  SCM_VALIDATE_BYTEVECTOR (SCM_ARG1, pollfds);
  c_nfds = scm_to_uint32 (nfds);
  c_timeout = scm_to_int (timeout);
  
  if (SCM_UNLIKELY (SCM_BYTEVECTOR_LENGTH (pollfds)
                    < c_nfds * sizeof(struct pollfd)))
    SCM_OUT_OF_RANGE (SCM_ARG2, nfds);
  
  SCM_VALIDATE_VECTOR (SCM_ARG3, ports);
  if (SCM_UNLIKELY (SCM_SIMPLE_VECTOR_LENGTH (ports) < c_nfds))
    SCM_OUT_OF_RANGE (SCM_ARG3, ports);
    
  fds = (struct pollfd*)SCM_BYTEVECTOR_CONTENTS (pollfds);
  
  for (i = 0; i < c_nfds; i++)
    {
      SCM port = SCM_SIMPLE_VECTOR_REF (ports, i);
      short int revents = 0;

      if (SCM_PORTP (port))
        {
          if (SCM_CLOSEDP (port))
            revents |= POLLERR;
          else
            {
              scm_t_port *pt = SCM_PTAB_ENTRY (port);

              if (pt->read_pos < pt->read_end)
                /* Buffered input waiting to be read. */
                revents |= POLLIN;
              if (pt->write_pos < pt->write_end)
                /* Buffered output possible. */
                revents |= POLLOUT;
            }
        }

      if (revents & fds[i].events)
        {
          have_buffered_io = 1;
          c_timeout = 0;
          break;
        }
    }

  SCM_SYSCALL (rv = poll (fds, c_nfds, c_timeout));

  if (rv == -1)
    SCM_SYSERROR;

  if (have_buffered_io)
    for (i = 0; i < c_nfds; i++)
      {
        SCM port = SCM_SIMPLE_VECTOR_REF (ports, i);
        short int revents = 0;

        if (SCM_PORTP (port))
          {
            if (SCM_CLOSEDP (port))
              revents |= POLLERR;
            else
              {
                scm_t_port *pt = SCM_PTAB_ENTRY (port);

                if (pt->read_pos < pt->read_end)
                  /* Buffered input waiting to be read. */
                  revents |= POLLIN;
                if (SCM_OUTPUT_PORT_P (port) && pt->write_pos < pt->write_end)
                  /* Buffered output possible. */
                  revents |= POLLOUT;
              }
          }

        /* Mask in the events we are interested, and test if any are
           interesting. */
        if ((revents &= fds[i].events))
          {
            /* Could be the underlying fd is also ready for reading.  */
            if (!fds[i].revents)
              rv++;

            /* In any case, add these events to whatever the syscall
               set. */
            fds[i].revents |= revents;
          }
      }

  return scm_from_int (rv);
}
#undef FUNC_NAME
#endif /* HAVE_POLL */




/* {EPoll}
 */

/* EPoll is a newer Linux interface designed for sets of file
   descriptors that are mostly in a dormant state.  These primitives
   wrap the epoll interface on a very low level.

   This is a low-level interface.  See the `(ice-9 epoll)' module for a more
   usable wrapper.  Note that this low-level interface deals in file
   descriptors, not ports, in order to allow higher-level code to handle
   the interaction with the garbage collector.  */
#ifdef HAVE_EPOLL
static SCM
scm_primitive_epoll_create (SCM cloexec_p)
#define FUNC_NAME "epoll-create"
{
  int fd;

#ifdef HAVE_EPOLL_CREATE1
  fd = epoll_create1 (scm_is_true (cloexec_p) ? EPOLL_CLOEXEC : 0);
  if (fd < 0)
    SCM_SYSERROR;
#else
  fd = epoll_create (16);
  if (fd < 0)
    SCM_SYSERROR;
  if (scm_is_true (cloexec_p))
    fcntl (fd, F_SETFD, FD_CLOEXEC, 1);
#endif

  return scm_from_int (fd);
}
#undef FUNC_NAME

/* This epoll wrapper always places the fd itself as the "data" of the
   events structure.  */
static SCM
scm_primitive_epoll_ctl (SCM epfd, SCM op, SCM fd, SCM events)
#define FUNC_NAME "primitive-epoll-ctl"
{
  int c_epfd, c_op, c_fd;
  struct epoll_event ev = { 0, };

  c_epfd = scm_to_int (epfd);
  c_op = scm_to_int (op);
  c_fd = scm_to_int (fd);

  if (SCM_UNBNDP (events))
    {
      if (c_op == EPOLL_CTL_DEL)
        /* Events do not matter in this case.  */
        ev.events = 0;
      else
        SCM_MISC_ERROR ("missing events arg", SCM_EOL);
    }
  else
    ev.events = scm_to_uint32 (events);

  ev.data.fd = c_fd;

  if (epoll_ctl (c_epfd, c_op, c_fd, &ev))
    SCM_SYSERROR;
  
  return SCM_UNSPECIFIED;
}
#undef FUNC_NAME

/* Wait on the files whose descriptors were registered on EPFD, and
   write the resulting events in EVENTSV, a bytevector.  Returns the
   number of struct epoll_event values that were written to EVENTSV,
   which may be zero if no files triggered wakeups within TIMEOUT
   milliseconds.  */
static SCM
scm_primitive_epoll_wait (SCM epfd, SCM eventsv, SCM timeout)
#define FUNC_NAME "primitive-epoll-wait"
{
  int c_epfd, maxevents, rv, c_timeout;
  struct epoll_event *events;

  c_epfd = scm_to_int (epfd);

  SCM_VALIDATE_BYTEVECTOR (SCM_ARG2, eventsv);
  if (SCM_UNLIKELY (SCM_BYTEVECTOR_LENGTH (eventsv) % sizeof (*events)))
    SCM_OUT_OF_RANGE (SCM_ARG2, eventsv);

  events = (struct epoll_event *) SCM_BYTEVECTOR_CONTENTS (eventsv);
  maxevents = SCM_BYTEVECTOR_LENGTH (eventsv) / sizeof (*events);
  c_timeout = SCM_UNBNDP (timeout) ? -1 : scm_to_int (timeout);

  SCM_SYSCALL (rv = epoll_wait (c_epfd, events, maxevents, c_timeout));

  if (rv == -1)
    SCM_SYSERROR;

  return scm_from_int (rv);
}
#undef FUNC_NAME

#endif /* HAVE_EPOLL */




/* Low-level helpers for (ice-9 poll).  */
static void
scm_init_poll (void)
{
#if HAVE_POLL
  scm_c_define_gsubr ("primitive-poll", 4, 0, 0, scm_primitive_poll);
  scm_c_define ("%sizeof-struct-pollfd", scm_from_size_t (sizeof (struct pollfd)));
#else
  scm_misc_error ("%init-poll", "`poll' unavailable on this platform", SCM_EOL);
#endif

#ifdef POLLIN
  scm_c_define ("POLLIN", scm_from_int (POLLIN));
#endif 	       
#ifdef POLLPRI
  scm_c_define ("POLLPRI", scm_from_int (POLLPRI));
#endif 	       
#ifdef POLLOUT
  scm_c_define ("POLLOUT", scm_from_int (POLLOUT));
#endif 	       
#ifdef POLLRDHUP
  scm_c_define ("POLLRDHUP", scm_from_int (POLLRDHUP));
#endif 	       
#ifdef POLLERR
  scm_c_define ("POLLERR", scm_from_int (POLLERR));
#endif 	       
#ifdef POLLHUP
  scm_c_define ("POLLHUP", scm_from_int (POLLHUP));
#endif 	       
#ifdef POLLNVAL
  scm_c_define ("POLLNVAL", scm_from_int (POLLNVAL));
#endif 	       

}

/* Low-level helpers for (ice-9 epoll).  */
static void
scm_init_epoll (void)
{
#ifdef HAVE_EPOLL
  scm_c_define_gsubr ("primitive-epoll-create", 1, 0, 0,
                      scm_primitive_epoll_create);
  scm_c_define_gsubr ("primitive-epoll-ctl", 3, 1, 0,
                      scm_primitive_epoll_ctl);
  scm_c_define_gsubr ("primitive-epoll-wait", 3, 1, 0,
                      scm_primitive_epoll_wait);
  scm_c_define ("%sizeof-struct-epoll-event",
                scm_from_size_t (sizeof (struct epoll_event)));
  scm_c_define ("%offsetof-struct-epoll-event-fd",
                scm_from_size_t (offsetof (struct epoll_event, data.fd)));
  scm_c_define ("EPOLLIN", scm_from_int (EPOLLIN));
  scm_c_define ("EPOLLOUT", scm_from_int (EPOLLOUT));
#ifdef EPOLLRDHUP
  scm_c_define ("EPOLLRDHUP", scm_from_int (EPOLLRDHUP));
#endif
  scm_c_define ("EPOLLPRI", scm_from_int (EPOLLPRI));
  scm_c_define ("EPOLLERR", scm_from_int (EPOLLERR));
  scm_c_define ("EPOLLHUP", scm_from_int (EPOLLHUP));
  scm_c_define ("EPOLLET", scm_from_int (EPOLLET));
#ifdef EPOLLONESHOT
  scm_c_define ("EPOLLONESHOT", scm_from_int (EPOLLONESHOT));
#endif
  scm_c_define ("EPOLL_CTL_ADD", scm_from_int (EPOLL_CTL_ADD));
  scm_c_define ("EPOLL_CTL_MOD", scm_from_int (EPOLL_CTL_MOD));
  scm_c_define ("EPOLL_CTL_DEL", scm_from_int (EPOLL_CTL_DEL));
#else
  scm_misc_error ("%init-epoll", "`epoll' unavailable on this platform", SCM_EOL);
#endif
}

void
scm_register_poll (void)
{
  scm_c_register_extension ("libguile-" SCM_EFFECTIVE_VERSION,
                            "scm_init_poll",
			    (scm_t_extension_init_func) scm_init_poll,
			    NULL);

  scm_c_register_extension ("libguile-" SCM_EFFECTIVE_VERSION,
                            "scm_init_epoll",
			    (scm_t_extension_init_func) scm_init_epoll,
			    NULL);
}

/*
  Local Variables:
  c-file-style: "gnu"
  End:
*/
