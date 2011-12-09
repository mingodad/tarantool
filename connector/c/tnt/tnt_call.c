
/*
 * Copyright (C) 2011 Mail.RU
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#include <tnt_proto.h>
#include <tnt_enc.h>
#include <tnt_tuple.h>
#include <tnt_reply.h>
#include <tnt_stream.h>
#include <tnt_call.h>

struct tnt_header_call {
	uint32_t flags;
};

/*
 * tnt_call()
 *
 * write call request to stream;
 *
 * s     - stream pointer
 * flags - request flags
 * proc  - remote procedure name
 * args  - call arguments
 * 
 * returns number of bytes written, or -1 on error.
*/
ssize_t
tnt_call(struct tnt_stream *s, uint32_t flags, char *proc,
	 struct tnt_tuple *args)
{
	/* encoding procedure name */
	int proc_len = strlen(proc);
	int proc_enc_size = tnt_enc_size(proc_len);
	char proc_enc[5];
	tnt_enc_write(proc_enc, proc_len);
	/* filling major header */
	struct tnt_header hdr;
	hdr.type = TNT_OP_CALL;
	hdr.len = sizeof(struct tnt_header_call) +
		  proc_enc_size + proc_len + args->size;
	hdr.reqid = s->reqid;
	/* filling call header */
	struct tnt_header_call hdr_call;
	hdr_call.flags = flags;
	/* writing data to stream */
	struct iovec v[5];
	v[0].iov_base = &hdr;
	v[0].iov_len  = sizeof(struct tnt_header);
	v[1].iov_base = &hdr_call;
	v[1].iov_len  = sizeof(struct tnt_header_call);
	v[2].iov_base = proc_enc;
	v[2].iov_len  = proc_enc_size;
	v[3].iov_base = proc;
	v[3].iov_len  = proc_len;
	v[4].iov_base = args->data;
	v[4].iov_len  = args->size;
	return s->writev(s, v, 5);
}