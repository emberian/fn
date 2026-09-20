/*	fn_ltp_stage.c -- durable inbound staging for an ION BP endpoint.

	ION has no non-destructive receive.  bp_receive() deletes the
	delivery-queue element, zeroes bundle.payload.content and destroys
	the bundle inside one SDR transaction that it commits before it
	returns, so after it returns the bundle is gone from the endpoint
	and the payload ZCO exists only as a reference in this process.
	bprecvfile then write()s that payload to testfile<N> with no fsync,
	no rename and a per-process counter, so a restart both loses
	unflushed bytes and reuses file names.

	This program is the app-level staging copy fn needs instead: it
	takes delivery, writes the exact ADU to a temporary file, fsyncs the
	file, renames it into the staging directory under a name derived
	from the BP bundle id, fsyncs that directory, and only then releases
	the delivery.  The residual crash window between bp_receive()'s
	commit and this fsync cannot be closed with ION's public API; it is
	covered at the fn layer by durable sender work and retry, not by the
	BPA.  Staging here is not fn acceptance, validation or a receipt.	*/

#include <bp.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>

#define FN_MAX_ADU 65538

static int	stageAdu(char *dir, char *bid, char *buf, int len)
{
	char	tmp[1024];
	char	final[1024];
	int	fd;
	int	dirfd;

	isprintf(tmp, sizeof tmp, "%s/.staging-tmp", dir);
	isprintf(final, sizeof final, "%s/%s", dir, bid);
	fd = open(tmp, O_WRONLY | O_CREAT | O_TRUNC, 0600);
	if (fd < 0) return -1;
	if (write(fd, buf, len) != len) { close(fd); return -1; }
	if (fsync(fd) < 0) { close(fd); return -1; }
	if (close(fd) < 0) return -1;
	if (rename(tmp, final) < 0) return -1;
	dirfd = open(dir, O_RDONLY);
	if (dirfd < 0) return -1;
	if (fsync(dirfd) < 0) { close(dirfd); return -1; }
	close(dirfd);
	return 0;
}

int	main(int argc, char **argv)
{
	char		*ownEid;
	char		*stageDir;
	int		timeout;
	BpSAP		sap;
	Sdr		sdr;
	BpDelivery	dlv;
	ZcoReader	reader;
	char		buf[FN_MAX_ADU];
	char		bid[512];
	vast		len;
	int		staged = 0;

	if (argc < 4)
	{
		fprintf(stderr, "usage: fn_ltp_stage <ownEid> <stageDir> "
				"<timeoutSeconds> [<count>]\n");
		return 1;
	}

	ownEid = argv[1];
	stageDir = argv[2];
	timeout = atoi(argv[3]);
	int wanted = (argc > 4) ? atoi(argv[4]) : 1;

	if (bp_attach() < 0) { fprintf(stderr, "bp_attach failed\n"); return 1; }
	if (bp_open(ownEid, &sap) < 0)
	{
		fprintf(stderr, "bp_open %s failed\n", ownEid);
		return 1;
	}

	sdr = bp_get_sdr();
	while (staged < wanted)
	{
		if (bp_receive(sap, &dlv, timeout) < 0)
		{
			fprintf(stderr, "bp_receive failed\n");
			break;
		}

		if (dlv.result == BpReceptionTimedOut
		|| dlv.result == BpEndpointStopped)
		{
			bp_release_delivery(&dlv, 1);
			break;
		}

		if (dlv.result != BpPayloadPresent)
		{
			bp_release_delivery(&dlv, 1);
			continue;
		}

		len = zco_source_data_length(sdr, dlv.adu);
		if (len <= 0 || len > FN_MAX_ADU)
		{
			/*	Outside the bounded fn laboratory profile.	*/
			fprintf(stderr, "refused ADU of " VAST_FIELDSPEC
					" octets\n", len);
			bp_release_delivery(&dlv, 1);
			continue;
		}

		zco_start_receiving(dlv.adu, &reader);
		if (sdr_begin_xn(sdr) < 0) { bp_release_delivery(&dlv, 1); break; }
		if (zco_receive_source(sdr, &reader, len, buf) < 0)
		{
			sdr_cancel_xn(sdr);
			bp_release_delivery(&dlv, 1);
			break;
		}

		if (sdr_end_xn(sdr) < 0) { bp_release_delivery(&dlv, 1); break; }

		/*	The staged name is the BP bundle id fn would bind
		 *	its attempt to: source EID, creation time, counter.	*/
		isprintf(bid, sizeof bid, "%s|%lu|%lu",
				dlv.bundleSourceEid,
				(unsigned long) dlv.bundleCreationTime.msec,
				(unsigned long) dlv.bundleCreationTime.count);
		for (char *p = bid; *p; p++)
		{
			if (*p == '/') *p = '_';
		}

		if (stageAdu(stageDir, bid, buf, (int) len) < 0)
		{
			fprintf(stderr, "durable staging failed for %s\n", bid);
			bp_release_delivery(&dlv, 1);
			break;
		}

		printf("staged %s " VAST_FIELDSPEC "\n", bid, len);
		fflush(stdout);
		bp_release_delivery(&dlv, 1);
		staged++;
	}

	bp_close(sap);
	bp_detach();
	return staged > 0 ? 0 : 2;
}
