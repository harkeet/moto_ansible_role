#!/usr/bin/perl

###############################################################################
#
# Motorola Ping Polling script
#
# This script is designed to ping a large number of IPs in a set time interval,
# and generate SNMP traps when the up/down status of an IP changes. All
# configuration and runtime data is stored in a MySQL database. The script
# should be run from cron every 5 minutes.
#
# Run the command "MOTO_POLL help" for command line help.
#
#		v 1.0	5/30/2012	Ulysses Cruz
#		v 1.1	6/1/2012	Ulysses Cruz	Adapted to work with addsourceip script
#		v 1.2	6/8/2012	Ulysses Cruz	Added status reporting functionality
#		v 1.3	6/14/2012	Ulysses Cruz	Added NBI configuration into db
#		v 2.0	6/19/2012	Ulysses Cruz	Added multi-host shared configuration capability, Configuration can now be backed up and restored.new script locking mechanism in place allowing finer control. Added function to automatically upgrade old v1.x configuration.
#		v 2.1	7/6/2012	Ulysses Cruz	Added thread limiting to avoid crashes on extremely large device lists, and mysql queueing to prevent update failures.
#		v 3.0	7/16/2012	Ulysses Cruz	Re-implemented in perl script to improve performance.
#		v 4.0	9/28/2012	Ulysses Cruz	Added functionality for SNMP polling of switches and TCP pings of all devices
#		v 4.1	10/8/2012	Ulysses Cruz	Added reporting of failed SNMP polls on RFS switches.
#		v 5.0	10/23/2012	Ulysses Cruz	Converted debug flag to command line option, integrated netcool local version into mainline.
#		v 5.1	10/31/2012	Ulysses Cruz	Cleaned up code, added additional comments and streamlined flow
#		v 5.2	2/4/2013	Ulysses Cruz	Added continuous down notification option, to resend down events at every poll cycle.
#		v 5.3	10/10/2013	Ulysses Cruz	Modified polling timeouts and thread counts to provide more efficient use during internet polling.
#		v 5.4	11/25/2014	Ulysses Cruz	Allow short notes to be assigned to each device entry, which will be included in any trap sent for that device.
#		v 5.5	12/1/2014	Ulysses Cruz	Corrected bugs with new database creation related to the new config versioning code.
#
# ©2012 Ulysses Cruz, Motorola Solutions Inc.
###############################################################################
my $version  = '5.4';

$| = 1; # force buffer flush on each write

my $debug :shared = 0; # turn on debugging

use Config;
$Config{useithreads} or die('Recompile Perl with threads to run this program.');

use threads; # activate thread support
use threads::shared; # allow shared data between threads
use Thread::Queue; # shared queue support
use Thread::Semaphore; # process control semaphores
use POSIX qw(strftime); # allow for easy format of timestamps
use POSIX qw(nice); # allow the process to run 'nice' lowering priority
use Fcntl qw(:flock); # import the LOCK_?? flock constants
use Net::SNMP qw(:ALL); # allow perl native SNMP commands
use strict; # enable run-time error checking
use warnings; # enable run-time warnings

# Global variable
my $hostname = `hostname -s`; chomp($hostname); # grab only the short name of the host, prevent errors with periods in database table names
my $script = `basename $0`; chomp($script);
my @NBIS :shared;
my $CUSTOMER :shared;
my $start_time = strftime("%F %T", localtime);
my $finish_time;
my $device_total :shared = 0;
my $switch_total :shared = 0;
my $ap_total :shared = 0;
my $global_thread_limit = int(`cat /proc/sys/kernel/threads-max` / 256);
my $mysql_host = 'localhost';
my $mysql_user = 'root';
my $mysql_pass = '';

# Create control queues
my $device_known = Thread::Queue->new();
my $device_unknown = Thread::Queue->new();
my $switch_unknown = Thread::Queue->new();
my $ap_known = Thread::Queue->new();
my $status_message = Thread::Queue->new();

# Create process semaphore
my $trap_limit = Thread::Semaphore->new(2); # limit the number of simultaneous snmptraps being sent
my $queue_limit = Thread::Semaphore->new($global_thread_limit); # limit the size of the pending items queue
my $snmp_queue_limit = Thread::Semaphore->new($global_thread_limit); # limit the size of the pending items queue
my $start_polling = Thread::Semaphore->new(0); # control the startup of the poll master thread
my $stop_polling = Thread::Semaphore->new(0); # Control the shutdown of the poll master thread

################################################################################
#
# Main routine
#
################################################################################
nice(2); # raise the process nice value

my $add :shared = 0;
my $drop :shared = 0;
my $listadd :shared = 0;
my $listdrop :shared = 0;
my $snmpon :shared = 0;
my $snmpoff :shared = 0;
my $listsnmpon :shared = 0;
my $listsnmpoff :shared = 0;
my $snmpcom :shared =0;
my $tcpon :shared = 0;
my $tcpoff :shared = 0;
my $listtcpon :shared = 0;
my $listtcpoff :shared = 0;
my $pingport :shared = 0;
my $nbiadd :shared = 0;
my $nbidrop :shared = 0;
my $customer :shared = 0;
my $hostupdate :shared = 0;
my $hostdelete :shared = 0;
my $noteadd :shared = 0;
my $notedrop :shared = 0;
my $status :shared = 0;
my $backup :shared = 0;
my $restore :shared = 0;
my $continuous :shared = 0;
my $lockfile = "/var/lock/motopoll" . "_" . $hostname;
my @device_info;

# Start thread thread to handle all print to stdout.
my $print_thread = threads->create(\&print_message);

if ( @ARGV > 0 ) { # A command line option has been set
	my $opts_thread = threads->create(\&get_opts);
	$opts_thread->join();

	# Process options
	if ( $hostupdate ) {
		$status_message->enqueue("Updating old host $hostupdate to $hostname in config.\n");
		open(LOCKFILE, ">>$lockfile") or &log_exit("Unable to open lockfile $lockfile");
		flock(LOCKFILE, LOCK_EX) or &log_exit("Exiting: poller session already running!");
		&database_interface('host_update', $hostupdate);
	} elsif ( $hostdelete ) {
		$status_message->enqueue("Deleting host $hostdelete from config.\n");
		open(LOCKFILE, ">>$lockfile") or &log_exit("Unable to open lockfile $lockfile");
		flock(LOCKFILE, LOCK_EX) or &log_exit("Exiting: poller session already running!");
		&database_interface('host_delete', $hostdelete);
	} elsif ( $nbiadd ) {
		$status_message->enqueue("Adding NBI $nbiadd\n") if ($debug);
		&database_interface('nbi_add', $nbiadd);
	} elsif ( $nbidrop ) {
		$status_message->enqueue("Dropping NBI $nbidrop\n") if ($debug);
		open(LOCKFILE, ">>$lockfile") or &log_exit("Unable to open lockfile $lockfile");
		flock(LOCKFILE, LOCK_EX) or &log_exit("Exiting: poller session already running!");
		&database_interface('nbi_drop', $nbidrop);
	} elsif ( $customer ) {
		$status_message->enqueue("Setting customer to $customer\n") if ($debug);
		&database_interface('customer', $customer);
	} elsif ( $add ) {
		my $db_thread = threads->create(\&database_interface,'device_add',0);
		while ($add =~ m/(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})/g) {
			$status_message->enqueue("Adding device $1\n");
			@device_info=($start_time, 'unknown', $start_time, NULL, 0, $1);
			$device_unknown->enqueue(\@device_info);
		}
		$device_unknown->enqueue('END');
		$db_thread->join();
	} elsif ( $drop ) {
		open(LOCKFILE, ">>$lockfile") or &log_exit("Unable to open lockfile $lockfile");
		flock(LOCKFILE, LOCK_EX) or &log_exit("Exiting: poller session already running!");
		my $db_thread = threads->create(\&database_interface,'device_drop',0);
		while ($drop =~ /(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})/g) {
			$status_message->enqueue("Dropping device $1\n");
			@device_info=($start_time, 'unknown', $start_time, NULL, 0, $1);
			$device_unknown->enqueue(\@device_info);
		}
		$device_unknown->enqueue('END');
		$db_thread->join();
	} elsif ( $listadd ) {
		$status_message->enqueue("Adding devices from $listadd\n") if ($debug);
		open(DATA, $listadd) || die("Could not open file $listadd");
		my $db_thread = threads->create(\&database_interface,'device_add',0);
		foreach my $line (<DATA>) {
			while ($line =~ /(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})/g) {
				$status_message->enqueue("Adding device $1\n");
				@device_info=($start_time, 'unknown', $start_time, NULL, 0, $1);
				$device_unknown->enqueue(\@device_info);
			}
		}
		$device_unknown->enqueue('END');
		$db_thread->join();
	} elsif ( $listdrop ) {
		$status_message->enqueue("Dropping devices from $listdrop\n") if ($debug);
		open(LOCKFILE, ">>$lockfile") or &log_exit("Unable to open lockfile $lockfile");
		flock(LOCKFILE, LOCK_EX) or &log_exit("Exiting: poller session already running!");
		open(DATA, $listdrop) || die("Could not open file $listdrop");
		my $db_thread = threads->create(\&database_interface,'device_drop',0);
		foreach my $line (<DATA>) {
			while ($line =~ /(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})/g) {
				$status_message->enqueue("Dropping device $1\n");
				@device_info=($start_time, 'unknown', $start_time, NULL, 0, $1);
				$device_unknown->enqueue(\@device_info);
			}
		}
		$device_unknown->enqueue('END');
		$db_thread->join();
	} elsif ( $noteadd ) {
		$status_message->enqueue("Adding notes to device from $noteadd\n") if ($debug);
		open(LOCKFILE, ">>$lockfile") or &log_exit("Unable to open lockfile $lockfile");
		flock(LOCKFILE, LOCK_EX) or &log_exit("Exiting: poller session already running!");
		open(DATA, $noteadd) || die("Could no open file $noteadd");
		my $db_thread = threads->create(\&database_interface,'note_add',0);
		foreach my $line (<DATA>) {
			chomp($line);
			$line =~ s/\s/ /g;
			my($device, $note) = split(/ /,$line,2);
			@device_info=($device, $note);
			$device_unknown->enqueue(\@device_info);
		}
		$device_unknown->enqueue('END');
		$db_thread->join();
	} elsif ( $notedrop ) {
		$status_message->enqueue("Dropping device notes from $notedrop\n") if ($debug);
		open(LOCKFILE, ">>$lockfile") or &log_exit("Unable to open lockfile $lockfile");
		flock(LOCKFILE, LOCK_EX) or &log_exit("Exiting: poller session already running!");
		open(DATA, $notedrop) || die("Could no open file $notedrop");
		my $db_thread = threads->create(\&database_interface,'note_drop',0);
		foreach my $line (<DATA>) {
			while ($line =~ /(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})/g) {
				$status_message->enqueue("Dropping note on device $1\n");
				@device_info=($1, $start_time);
				$device_unknown->enqueue(\@device_info);
			}
		}
		$device_unknown->enqueue('END');
		$db_thread->join();
	} elsif ( $snmpon ) {
		my $db_thread = threads->create(\&database_interface,'snmp_on',$snmpcom);
		while ($snmpon =~ m/(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})/g) {
			$status_message->enqueue("Activating SNMP poll of device $1 with community $snmpcom\n");
			@device_info=($start_time, 'unknown', $start_time, $snmpcom, 0, $1);
			$device_unknown->enqueue(\@device_info);
		}
		$device_unknown->enqueue('END');
		$db_thread->join();
	} elsif ( $snmpoff ) {
		open(LOCKFILE, ">>$lockfile") or &log_exit("Unable to open lockfile $lockfile");
		flock(LOCKFILE, LOCK_EX) or &log_exit("Exiting: poller session already running!");
		my $db_thread = threads->create(\&database_interface,'snmp_off',0);
		while ($snmpoff =~ /(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})/g) {
			$status_message->enqueue("Deactivating SNMP poll of device $1\n");
			@device_info=($start_time, 'unknown', $start_time, NULL, 0, $1);
			$device_unknown->enqueue(\@device_info);
		}
		$device_unknown->enqueue('END');
		$db_thread->join();
	} elsif ( $listsnmpon ) {
		$status_message->enqueue("Activating SNMP poll for devices from $listadd\n") if ($debug);
		open(DATA, $listsnmpon) || die("Could not open file $listadd");
		my $db_thread = threads->create(\&database_interface,'snmp_on',$snmpcom);
		foreach my $line (<DATA>) {
			while ($line =~ /(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})/g) {
				$status_message->enqueue("Activating SNMP poll of device $1 with community $snmpcom\n");
				@device_info=($start_time, 'unknown', $start_time, $snmpcom, 0, $1);
				$device_unknown->enqueue(\@device_info);
			}
		}
		$device_unknown->enqueue('END');
		$db_thread->join();
	} elsif ( $listsnmpoff ) {
		$status_message->enqueue("Deactivating SNMP poll of devices from $listdrop\n") if ($debug);
		open(LOCKFILE, ">>$lockfile") or &log_exit("Unable to open lockfile $lockfile");
		flock(LOCKFILE, LOCK_EX) or &log_exit("Exiting: poller session already running!");
		open(DATA, $listsnmpoff) || die("Could not open file $listdrop");
		my $db_thread = threads->create(\&database_interface,'snmp_off',0);
		foreach my $line (<DATA>) {
			while ($line =~ /(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})/g) {
				$status_message->enqueue("Deactivating SNMP poll of device $1\n");
				@device_info=($start_time, 'unknown', $start_time, NULL, 0, $1);
				$device_unknown->enqueue(\@device_info);
			}
		}
		$device_unknown->enqueue('END');
		$db_thread->join();
	} elsif ( $tcpon ) {
		my $db_thread = threads->create(\&database_interface,'tcp_on',$pingport);
		while ($tcpon =~ m/(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})/g) {
			$status_message->enqueue("Activating TCP ping for device $1\n");
			@device_info=($start_time, 'unknown', $start_time, NULL, $pingport, $1);
			$device_unknown->enqueue(\@device_info);
		}
		$device_unknown->enqueue('END');
		$db_thread->join();
	} elsif ( $tcpoff ) {
		open(LOCKFILE, ">>$lockfile") or &log_exit("Unable to open lockfile $lockfile");
		flock(LOCKFILE, LOCK_EX) or &log_exit("Exiting: poller session already running!");
		my $db_thread = threads->create(\&database_interface,'tcp_off',0);
		while ($tcpoff =~ /(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})/g) {
			$status_message->enqueue("Deactivating TCP ping for device $1\n");
			@device_info=($start_time, 'unknown', $start_time, NULL, 0, $1);
			$device_unknown->enqueue(\@device_info);
		}
		$device_unknown->enqueue('END');
		$db_thread->join();
	} elsif ( $listtcpon ) {
		$status_message->enqueue("Activating TCP ping for devices from $listadd\n") if ($debug);
		open(DATA, $listtcpon) || die("Could not open file $listadd");
		my $db_thread = threads->create(\&database_interface,'tcp_on',$pingport);
		foreach my $line (<DATA>) {
			while ($line =~ /(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})/g) {
				$status_message->enqueue("Activating TCP ping for device $1\n");
				@device_info=($start_time, 'unknown', $start_time, NULL, $pingport, $1);
				$device_unknown->enqueue(\@device_info);
			}
		}
		$device_unknown->enqueue('END');
		$db_thread->join();
	} elsif ( $listtcpoff ) {
		$status_message->enqueue("Deactivating TCP ping for devices from $listdrop\n") if ($debug);
		open(LOCKFILE, ">>$lockfile") or &log_exit("Unable to open lockfile $lockfile");
		flock(LOCKFILE, LOCK_EX) or &log_exit("Exiting: poller session already running!");
		open(DATA, $listtcpoff) || die("Could not open file $listdrop");
		my $db_thread = threads->create(\&database_interface,'tcp_off',0);
		foreach my $line (<DATA>) {
			while ($line =~ /(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})/g) {
				$status_message->enqueue("Deactivating TCP ping for device $1\n");
				@device_info=($start_time, 'unknown', $start_time, NULL, 0, $1);
				$device_unknown->enqueue(\@device_info);
			}
		}
		$device_unknown->enqueue('END');
		$db_thread->join();
	} elsif ( $backup ) {
		$status_message->enqueue("Backing up the configuration to $backup\n");
		`mysqldump -u $mysql_user --databases moto_poll > $backup`;
	} elsif ( $restore ) {
		$status_message->enqueue("Restoring configuration from $restore\n");
		`mysql -u $mysql_user < $restore`;
	} elsif ( $status ) {
		if ($status eq 'devices') {
			&database_interface('global');
			$status_message->enqueue("Current status of all monitored devices:\n");
			my $format='| %6$-15s | %1$-19s | %2$-7s | %3$-19s | %4$-20s | %5$-5s |' . "\n";
			$status_message->enqueue("+-----------------+---------------------+---------+---------------------+----------------------+-------+\n");
			$status_message->enqueue(sprintf($format,'LAST POLL','STATUS','LAST CHANGED','COMMUNITY','PORT','IP'));
			$status_message->enqueue("+-----------------+---------------------+---------+---------------------+----------------------+-------+\n");
			my $list_devices = threads->create(\&database_interface,'device_stat');
			while (my $device_ref = $device_unknown->dequeue()) {
				last if ($device_ref eq 'END');
				my @device_info = @$device_ref;
				for (my $count = 0 ; $count <= 5 ; $count++) {
					$device_info[$count] = 'NULL' unless ($device_info[$count])
				}
				$status_message->enqueue(sprintf($format,@device_info));
				$queue_limit->up();
			}
			$status_message->enqueue("+-----------------+---------------------+---------+---------------------+----------------------+-------+\n");
		} elsif ($status eq 'aps') {
			&database_interface('global');
			$status_message->enqueue("Current status of all monitored APs:\n");
			my $format='| %3$-15s | %4$-19s | %1$-9s |' . "\n";
			$status_message->enqueue("+-----------------+---------------------+-----------+\n");
			$status_message->enqueue(sprintf($format,'LAST STAT','','SWITCH','NAME'));
			$status_message->enqueue("+-----------------+---------------------+-----------+\n");
			my $list_aps = threads->create(\&database_interface,'ap_stat');
			while (my $ap_ref = $ap_known->dequeue()) {
				last if ($ap_ref eq 'END');
				my @ap_info = @$ap_ref;
				for (my $count = 0 ; $count <= 5 ; $count++) {
					$ap_info[$count] = 'NULL' unless ($ap_info[$count])
				}
				$status_message->enqueue(sprintf($format,@ap_info));
				$queue_limit->up();
			}
			$status_message->enqueue("+-----------------+---------------------+-----------+\n");
		} elsif ($status eq 'poller') {
			$status_message->enqueue("\nCurrent status of the poller(s):\n\n");
			my $list_devices = threads->create(\&database_interface,'host_list');
			$status_message->enqueue("+----------------------+----------------------+---------------------+---------------------+---------------------+\n");
			my $format="| %-20s | %-20s | %-19s | %-19s | %-19s |\n";
			$status_message->enqueue(sprintf($format,'POLLER','CUSTOMER','LAST POLL START','LAST POLL END','CURRENT POLL START'));
			$status_message->enqueue("+----------------------+----------------------+---------------------+---------------------+---------------------+\n");
			while (my $device_ref = $device_unknown->dequeue()) {
				last if ($device_ref eq 'END');
				my @device_info = @$device_ref;
				for (my $count = 0 ; $count <= 4 ; $count++) {
					$device_info[$count] = 'NULL' unless ($device_info[$count])
				}
				$status_message->enqueue(sprintf($format,@device_info));
				$queue_limit->up();
			}
			$status_message->enqueue("+----------------------+----------------------+---------------------+---------------------+---------------------+\n");
			$status_message->enqueue("\nNBIs for host $hostname:\n");
			foreach my $nbi (@NBIS) {
				$status_message->enqueue("$nbi\n");
			}
			$status_message->enqueue("\nNumber of devices polled: $device_total\n");
			$status_message->enqueue("\nNumber of RFS switches polled: $switch_total\n");
			$status_message->enqueue("\nNumber of APs polled: $ap_total\n\n");
		} elsif ($status eq 'resend') {
			$status_message->enqueue("Resending all devices status\n");
			&database_interface('global');
			my $list_devices = threads->create(\&database_interface,'device_list');
			while (my $device_ref = $device_unknown->dequeue()) {
				last if ($device_ref eq 'END');
				my ($last_poll, $last_stat, $last_chng, $community, $port, $ip, $note) = @$device_ref;
				my $curr = strftime("%F %T", localtime);
				$status_message->enqueue("Device $ip last status: $last_stat\n");
				if ($last_stat eq 'down') {
					$status_message->enqueue("Node down: $ip\n");
					&send_trap($ip,"Node failure. $ip at $curr from $hostname.",$note);
				} elsif ($last_stat eq 'up') {
					$status_message->enqueue("Node up: $ip\n");
					&send_trap($ip,"Node clear. $ip at $curr from $hostname.",$note);
				}
				$queue_limit->up();
			}
			my $list_aps = threads->create(\&database_interface,'ap_stat');
			while (my $ap_ref = $ap_known->dequeue()) {
				last if ($ap_ref eq 'END');
				my ($last_stat, $polled, $switch, $name) = @$ap_ref;
				my $curr = strftime("%F %T", localtime);
				$status_message->enqueue("AP $name last status: $last_stat\n");
				if ($last_stat eq 'down') {
					$status_message->enqueue("AP unadopt: $name\n");
					&send_trap($name,"AP unadopt. $name at $curr from $switch.","");
				} elsif ($last_stat eq 'up') {
					$status_message->enqueue("AP adopt: $name\n");
					&send_trap($name,"AP adopt. $name at $curr from $switch.","");
				}
				$queue_limit->up();
			}
		} elsif ($status eq 'notes') {
			&database_interface('global');
			$status_message->enqueue("Listing devices with notes:\n");
			my $border="+-----------------+" . "-" x 130 . "+\n";
			my $format='| %1$-15s | %2$-128s |' . "\n";
			$status_message->enqueue($border);
			$status_message->enqueue(sprintf($format, 'IP', 'NOTE'));
			$status_message->enqueue($border);
			my $list_notes = threads->create(\&database_interface,'note_list');
			while (my $device_ref = $device_unknown->dequeue()) {
				last if ($device_ref eq 'END');
				my @device_info = @$device_ref;
				$status_message->enqueue(sprintf($format,@device_info));
				$queue_limit->up();
			}
			$status_message->enqueue($border);
		} else {
			$status_message->enqueue("Checking the status of device $status:\n\n");
			my @switches;
			my $format='| %6$-15s | %1$-19s | %2$-7s | %3$-19s | %4$-20s | %5$-5s |' . "\n";
			$status_message->enqueue("+-----------------+---------------------+---------+---------------------+----------------------+-------+\n");
			$status_message->enqueue(sprintf($format,'LAST POLL','STATUS','LAST CHANGED','COMMUNITY','PORT','IP'));
			$status_message->enqueue("+-----------------+---------------------+---------+---------------------+----------------------+-------+\n");
			my $list_devices = threads->create(\&database_interface,'device_search',$status);
			while (my $device_ref = $device_unknown->dequeue()) {
				last if ($device_ref eq 'END');
				my @device_info = @$device_ref;
				if ($device_info[3]) {
					$status_message->enqueue("Switch found: $device_info[5]\n") if ($debug);
					push(@switches, $device_info[5]);
				}
				for (my $count = 0 ; $count <= 6 ; $count++) {
					$device_info[$count] = 'NULL' unless ($device_info[$count])
				}
				$status_message->enqueue(sprintf($format,@device_info));
			}
			$status_message->enqueue("+-----------------+---------------------+---------+---------------------+----------------------+-------+\n");
			$status_message->enqueue("\nCurrent status of all associated APs:\n");
			$format='| %3$-15s | %4$-19s | %1$-9s |' . "\n";
			$status_message->enqueue("+-----------------+---------------------+-----------+\n");
			$status_message->enqueue(sprintf($format,'LAST STAT','','SWITCH','NAME'));
			$status_message->enqueue("+-----------------+---------------------+-----------+\n");
			my $list_aps = threads->create(\&database_interface,'ap_search',\@switches);
			while (my $ap_ref = $ap_known->dequeue()) {
				last if ($ap_ref eq 'END');
				my @ap_info = @$ap_ref;
				$status_message->enqueue("AP: @ap_info\n") if ($debug);
				for (my $count = 0 ; $count <= 3 ; $count++) {
					$ap_info[$count] = 'NULL' unless ($ap_info[$count])
				}
				$status_message->enqueue(sprintf($format,@ap_info));
				$queue_limit->up();
			}
			$status_message->enqueue("+-----------------+---------------------+-----------+\n");
		}
	} elsif ($debug) { # Only the debug flag has been set, run a poll!
		&run_poll();
	} elsif ($continuous) { # Only the continuous down notification flag has been set, run a poll!
		&run_poll();
	}
} else { # No options set, run a poll!
	&run_poll();
}

$status_message->enqueue("END");

# Wait for all threads to finish processing
foreach my $threads (threads->list()) {
	$threads->join();
}

exit(0);

################################################################################
#
# Subroutines
#
################################################################################

# Subroutine to kick off a polling session
sub run_poll () {
	$status_message->enqueue("Starting MOTO_POLL\n");
	$status_message->enqueue("Running poll!\n") if ($debug);

	my $get_global = threads->new(\&database_interface,'global');
	$get_global->join();

	open(LOCKFILE, ">>$lockfile") or &log_exit("Unable to open lockfile $lockfile");
	flock(LOCKFILE, LOCK_EX | LOCK_NB) or &log_exit("Exiting: poller session already running!");

	my $start_sec = strftime("%s", localtime);
	my $poll_thread = threads->create(\&poll_master);
	$status_message->enqueue("Starting database threads\n") if ($debug);
	my $db_thread = threads->create(\&database_interface,'poll',0);

	foreach my $poll_threads ($db_thread, $poll_thread) {
		$poll_threads->join();
	}

	my $stop_sec = strftime("%s", localtime);
	$finish_time = strftime("%F %T", localtime);
	my $run_time = $stop_sec - $start_sec;

	&send_heartbeat($run_time);
	&log_only("Poll complete in $run_time seconds. Poller is alive.");

	close(LOCKFILE);
}


# Database Interface subroutine
sub database_interface () {

	# The DBI module is restricted to this subroutine to reduce memory utilization in the overall process
	require DBI;
	import DBI;

	my $function = $_[0];
	my $optional = $_[1];
	my $device_ref;
	my @device_info;
	my @ap_info;
	my $DB_version = 2;

	$status_message->enqueue("Starting database interface with function $function\n") if ($debug);

	# Create moto_poll database if it doesn't exist
	my $DB = DBI->connect("DBI:mysql:database=mysql;host=$mysql_host","$mysql_user","$mysql_pass") || &log_exit("Failed to connect to database: $DBI::errstr\n");
	$DB->do('create database if not exists moto_poll');
	$DB->disconnect;

	# Open moto_poll database
	$DB = DBI->connect("DBI:mysql:database=moto_poll;host=$mysql_host","$mysql_user","$mysql_pass") || &log_exit("Failed to connect to database: $DBI::errstr\n");

	# Perform database prep and maintenance
	$status_message->enqueue("Checking for configuration tables\n") if ($debug);
	my $table_exists = $DB->prepare("select count(*) from information_schema.TABLES where TABLE_SCHEMA='moto_poll' and TABLE_NAME='script'");
	$table_exists->execute();
	my $config_exists = $table_exists->fetchrow_array();
	$table_exists = undef;
	if ( ! $config_exists ) {
		# Tables don't exists so create them
		$status_message->enqueue("Creating new configuration tables\n") if ($debug);
		$DB->do("create table if not exists script (
			server		varchar(128) unique key default '$hostname',
			version		int,
			customer	varchar(128) default 'changeme',
			last_start	datetime,
			last_end	datetime,
			cur_start	datetime)");
		$DB->do("create table if not exists nbis_$hostname (
			ip		varchar(20) unique key)");
		$DB->do("create table if not exists devices_$hostname (
			ip			varchar(20) unique key,
			last_poll	datetime,
			last_stat	varchar(50) default 'unknown',
			last_chng	datetime,
			count		int default 0,
			priority	int default 0,
			snmp_comn	varchar(128),
			poll_port	int default 0,
			note		varchar(128))");
		$DB->do("create table if not exists aps_$hostname (
			switch		varchar(20) NOT NULL,
			name			varchar(128) NOT NULL,
			last_stat	varchar(50) default 'unknown',
			polled		boolean default false,
			unique key ap (switch,name))");
	} else {
		# The tables exist, check their version and update if necessary
		my $versioning = $DB->prepare("select count(*) from information_schema.COLUMNS where TABLE_SCHEMA='moto_poll' and TABLE_NAME='script' and COLUMN_NAME='version'");
		$versioning->execute();
		my $versioning_enabled = $versioning->fetchrow_array();
		$versioning = undef;
		if ( ! $versioning_enabled ) {
			# This is a table from before versioning was enabled, make the necessary changes!
			$status_message->enqueue("Updating global configuration tables\n") if ($debug);
			$DB->do("alter table script add column version int");
			$DB->do("alter table devices_$hostname change special1 snmp_comn varchar(128)");
			$DB->do("alter table devices_$hostname change special2 poll_port int default 0");
			$DB->do("alter table devices_$hostname add column note varchar(128)");
			$DB->do("update script set version=2 where server='$hostname'");
		} else {
			# config versioning is in place, check to make sure it's up to date:
			$status_message->enqueue("Checking if configuration tables for this host are up to date\n") if ($debug);
			my $table_version = $DB->prepare("select version from script where server='$hostname'");
			$table_version->execute();
			my $version = $table_version->fetchrow_array();
			$table_version = undef;
			if ( ! $version ) {
				# Versioning is enabled, but this host has none set, so it is an old version 1 host, update it's tables!
				$status_message->enqueue("Updating configuration tables\n") if ($debug);
				$DB->do("alter table devices_$hostname change special1 snmp_comn varchar(128)");
				$DB->do("alter table devices_$hostname change special2 poll_port int default 0");
				$DB->do("alter table devices_$hostname add column note varchar(128)");
				$DB->do("update script set version=2 where server='$hostname'");
			} else {
				$status_message->enqueue("All configuration tables are up to date\n") if ($debug);
			}
		}
	}

	# Prepare database commands
	my $sql_host_count = $DB->prepare("select count(*) from script where server=?");
	my $sql_host_add = $DB->prepare("insert ignore into script (server,version) values(?,?)");
	my $sql_host_start = $DB->prepare("update script set cur_start=? where server='$hostname'");
	my $sql_host_finish = $DB->prepare("update script set last_start=?,last_end=?,cur_start=NULL where server='$hostname'");
	my $sql_host_status = $DB->prepare("select server,customer,last_start,last_end,cur_start from script");
	my $sql_note_list = $DB->prepare("select ip,note from devices_$hostname where note is not null order by ip");
	my $sql_customer_get = $DB->prepare("select customer from script where server='$hostname'");
	my $sql_customer_set = $DB->prepare("update script set customer=? where server='$hostname'");
	my $sql_nbi_add = $DB->prepare("insert ignore into nbis_$hostname (ip) values (?)");
	my $sql_nbi_drop = $DB->prepare("delete from nbis_$hostname where ip=?");
	my $sql_nbi_query = $DB->prepare("select ip from nbis_$hostname");
	my $sql_device_add = $DB->prepare("insert ignore into devices_$hostname (ip) values (?)");
	my $sql_device_drop = $DB->prepare("delete from devices_$hostname where ip=?");
	my $sql_device_query = $DB->prepare("select last_poll,last_stat,last_chng,snmp_comn,poll_port,ip from devices_$hostname where ip like ?");
	my $sql_device_count = $DB->prepare("select count(*) from devices_$hostname");
	my $sql_device_status = $DB->prepare("select last_poll,last_stat,last_chng,snmp_comn,poll_port,ip from devices_$hostname order by last_chng asc");
	my $sql_snmp_on = $DB->prepare("update ignore devices_$hostname set snmp_comn=? where ip=?");
	my $sql_tcp_on = $DB->prepare("update ignore devices_$hostname set poll_port=? where ip=?");
	my $sql_tcp_off = $DB->prepare("update ignore devices_$hostname set poll_port=0 where ip=?");
	my $sql_ap_count = $DB->prepare("select count(*) from aps_$hostname");
	my $sql_ap_query = $DB->prepare("select sql_buffer_result last_stat,polled,switch,name from aps_$hostname where switch=?");
	my $sql_ap_status = $DB->prepare("select sql_buffer_result last_stat,polled,switch,name from aps_$hostname order by switch asc");
	my $sql_switch_count = $DB->prepare("select count(*) from devices_$hostname where snmp_comn !=''");

	# Make sure the current host is in the database, with the correct config version.
	$sql_host_add->execute($hostname,$DB_version);
	# Determine what database operations to perform based on indicated function
	if ( $function eq 'nbi_add' ) { # Add NBI to table for this host
		$sql_nbi_add->execute($optional);
		$status_message->enqueue("Added NBI $optional\n") if ($debug);
	} elsif ( $function eq 'nbi_drop' ) { # Drop NBI for this host
		$sql_nbi_drop->execute($optional);
		$status_message->enqueue("Dropped NBI $optional\n") if ($debug);
	} elsif ( $function eq 'customer' ) { # Change the customer name for this host
		$sql_customer_set->execute($optional);
		$status_message->enqueue("Set customer to $optional\n") if ($debug);
	} elsif ( $function eq 'device_add' ) { # Add one or more devices to the polling list
		while ($device_ref = $device_unknown->dequeue()) {
			last if ($device_ref eq 'END');
			@device_info = @$device_ref;
			$sql_device_add->execute($device_info[5]);
			$status_message->enqueue("Added device $device_info[5]\n") if ($debug);
		}
	} elsif ( $function eq 'device_drop' ) { # Drop one or more devices from the polling queue
		while ($device_ref = $device_unknown->dequeue()) {
			last if ($device_ref eq 'END');
			@device_info = @$device_ref;
			$sql_device_drop->execute($device_info[5]);
			$status_message->enqueue("Dropped device $device_info[5]\n") if ($debug);
		}
	} elsif ( $function eq 'note_add' ) { # Add a note to one or more devices
		while ($device_ref = $device_unknown->dequeue()) {
			last if ($device_ref eq 'END');
			@device_info = @$device_ref;
			$DB->do("update ignore devices_$hostname set note='$device_info[1]' where ip='$device_info[0]'");
			$status_message->enqueue("Added note to $device_info[0]: $device_info[1]\n");
		}
	} elsif ( $function eq 'note_drop' ) { # Drop a note from one or more devices
		while ($device_ref = $device_unknown->dequeue()) {
			last if ($device_ref eq 'END');
			@device_info = @$device_ref;
			$DB->do("update ignore devices_$hostname set note=NULL where ip='$device_info[0]'");
			$status_message->enqueue("Dropped note from device $device_info[0]\n") if ($debug);
		}
	} elsif ( $function eq 'note_list' ) { # Return the current status of all devices sorted by change time
		$sql_note_list->execute();
		while (my @device_info = $sql_note_list->fetchrow_array()) {
			$device_unknown->enqueue(\@device_info);
		}
		$device_unknown->enqueue('END');
	} elsif ( $function eq 'snmp_on' ) { # Activate SNMP for one or more devices
		while ($device_ref = $device_unknown->dequeue()) {
			last if ($device_ref eq 'END');
			@device_info = @$device_ref;
			$sql_snmp_on->execute($optional,$device_info[5]);
			$status_message->enqueue("Activated SNMP for device $device_info[5] with community $snmpcom\n") if ($debug);
		}
	} elsif ( $function eq 'snmp_off' ) { # Deactivate SNMP for one or more devices
		while ($device_ref = $device_unknown->dequeue()) {
			last if ($device_ref eq 'END');
			@device_info = @$device_ref;
			$DB->do("update ignore devices_$hostname set snmp_comn=NULL where ip='$device_info[5]'");
			$DB->do("delete ignore from aps_$hostname where switch='$device_info[5]'");
			$status_message->enqueue("Deactivated SNMP for device $device_info[5]\n") if ($debug);
		}
	} elsif ( $function eq 'tcp_on' ) { # Activate TCP pings for one or more devices
		while ($device_ref = $device_unknown->dequeue()) {
			last if ($device_ref eq 'END');
			@device_info = @$device_ref;
			$sql_tcp_on->execute($optional,$device_info[5]);
			$status_message->enqueue("Activated TCP for device $device_info[5]\n") if ($debug);
		}
	} elsif ( $function eq 'tcp_off' ) { # Deactivate TCP pings for one or more devices
		while ($device_ref = $device_unknown->dequeue()) {
			last if ($device_ref eq 'END');
			@device_info = @$device_ref;
			$sql_tcp_off->execute($device_info[5]);
			$status_message->enqueue("Activated TCP for device $device_info[5]\n") if ($debug);
		}
	} elsif ( $function eq 'device_list' ) { # Just list the current status of all devices
		my $db_reader = threads->create(\&device_reader);
		$db_reader->join();
	} elsif ( $function eq 'device_stat' ) { # Return the current status of all devices sorted by change time
		$sql_device_status->execute();
		while (my @device_info = $sql_device_status->fetchrow_array()) {
			$device_unknown->enqueue(\@device_info);
		}
		$device_unknown->enqueue('END');
	} elsif ( $function eq 'ap_stat' ) { # Return the current status of all devices sorted by change time
		$sql_ap_status->execute();
		while (my @ap_info = $sql_ap_status->fetchrow_array()) {
			$ap_known->enqueue(\@ap_info);
		}
		$ap_known->enqueue('END');
	} elsif ( $function eq 'device_search' ) { # Get the status of only a few devices
		$sql_device_query->execute($optional);
		while (@device_info = $sql_device_query->fetchrow_array()) {
			$device_unknown->enqueue(\@device_info);
		}
		$device_unknown->enqueue('END');
	} elsif ( $function eq 'ap_search' ) { # Get the status of only a few devices
		$status_message->enqueue("Looking up APs for switches: @$optional\n") if ($debug);
		foreach my $option (@$optional) {
			$sql_ap_query->execute($option);
			while (@ap_info = $sql_ap_query->fetchrow_array()) {
				$ap_known->enqueue(\@ap_info);
			}
		}
		$ap_known->enqueue('END');
	} elsif ( $function eq 'host_list') { # List the status information of the poll script
		$sql_device_count->execute();
		$device_total=$sql_device_count->fetchrow_array();
		$sql_switch_count->execute();
		$switch_total=$sql_switch_count->fetchrow_array();
		$sql_ap_count->execute();
		$ap_total=$sql_ap_count->fetchrow_array();
		$sql_nbi_query->execute();
		while (my $nbi = $sql_nbi_query->fetchrow_array()) {
			push(@NBIS,$nbi);
			$status_message->enqueue("Loaded NBI $nbi\n") if ($debug);
		}
		$sql_host_status->execute();
		while (my @host = $sql_host_status->fetchrow_array()) {
			$device_unknown->enqueue(\@host);
		}
		$device_unknown->enqueue('END');
	} elsif ( $function eq 'global') { # Load global variables
		$sql_customer_get->execute();
		$CUSTOMER = $sql_customer_get->fetchrow_array();
		$sql_device_count->execute();
		$device_total=$sql_device_count->fetchrow_array();
		$sql_switch_count->execute();
		$switch_total=$sql_switch_count->fetchrow_array();
		$sql_ap_count->execute();
		$ap_total=$sql_ap_count->fetchrow_array();
		$sql_nbi_query->execute();
		if ($CUSTOMER eq 'changeme') {
			$device_unknown->enqueue('END');
			&show_help();
			&log_exit("No customer set, aborting session!");
		}
		while (my $nbi = $sql_nbi_query->fetchrow_array()) {
			push(@NBIS,$nbi);
			$status_message->enqueue("Loaded NBI $nbi\n") if ($debug);
		}
	} elsif ( $function eq 'host_update' ) {
		$sql_host_count->execute($optional);
		if (my $count = $sql_host_count->fetchrow_array()) {
			$DB->do("delete from script where server='$hostname'");
			$DB->do("drop table nbis_$hostname");
			$DB->do("drop table devices_$hostname");
			$DB->do("drop table aps_$hostname");
			$DB->do("update script set server='$hostname' where server='$optional'");
			$DB->do("rename table nbis_$optional to nbis_$hostname");
			$DB->do("rename table devices_$optional to devices_$hostname");
			$DB->do("rename table aps_$optional to aps_$hostname");
		} else {
			$status_message->enqueue("Host $optional does not exist in the config!\n");
		}
	} elsif ( $function eq 'host_delete' ) {
		$sql_host_count->execute($optional);
		if (my $count = $sql_host_count->fetchrow_array()) {
			$DB->do("delete from script where server='$optional'");
			$DB->do("drop table nbis_$optional");
			$DB->do("drop table devices_$optional");
			$DB->do("drop table aps_$optional");
		} else {
			$status_message->enqueue("Host $optional does not exist in the config!\n");
		}
	} elsif ( $function eq 'poll') { # Setup for polling operations
		$sql_host_start->execute($start_time);

		# Start database read/write threads
		$status_message->enqueue("Starting device reader and writer:\n") if ($debug);
		my $dev_writer = threads->create(\&device_writer);
		my $dev_reader = threads->create(\&device_reader);
		$status_message->enqueue("Starting AP reader and writer:\n") if ($debug);
		my $ap_writer = threads->create(\&ap_writer);
#		my $ap_reader = threads->create(\&ap_reader);

		# Wait for all threads to finish processing
		foreach my $threads ($dev_reader,$dev_writer,$ap_writer) {
			$threads->join();
		}

		$sql_host_finish->execute($start_time,strftime("%F %T", localtime));
	}

	# Clean up the database connections before exiting
	$sql_host_count = undef;
	$sql_host_add = undef;
	$sql_host_start = undef;
	$sql_host_finish = undef;
	$sql_host_status = undef;
	$sql_note_list = undef;
	$sql_customer_get = undef;
	$sql_customer_set = undef;
	$sql_nbi_add = undef;
	$sql_nbi_drop = undef;
	$sql_nbi_query = undef;
	$sql_device_add = undef;
	$sql_device_drop = undef;
	$sql_device_query = undef;
	$sql_device_count = undef;
	$sql_device_status = undef;
	$sql_snmp_on = undef;
	$sql_tcp_on = undef;
	$sql_tcp_off = undef;
	$sql_ap_count = undef;
	$sql_ap_query = undef;
	$sql_ap_status = undef;
	$sql_switch_count = undef;

	$DB->disconnect;

	$status_message->enqueue("Stopped database interface with function $function.\n") if ($debug);
}

# Start device reader
sub device_reader () { # read the last know status of all devices from the databse
	# The DBI module is restricted to this subroutine to reduce memory utilization in the overall process
	require DBI;
	import DBI;

	undef($add);
	undef($drop);
	undef($listadd);
	undef($listdrop);
	undef($nbiadd);
	undef($nbidrop);
	undef($customer);
	undef($hostupdate);
	undef($hostdelete);
	undef($status);
	undef($backup);
	undef($restore);

	my $device_ref;
	my @device_info;

	$status_message->enqueue("Starting device reader.\n") if ($debug);

	# Open Database
	my $DB = DBI->connect("DBI:mysql:database=moto_poll;host=$mysql_host","$mysql_user","$mysql_pass") || &log_exit("Failed to connect to database: $DBI::errstr\n");

	# Prepare database commands
	my $sql_device_list = $DB->prepare("select sql_buffer_result last_poll,last_stat,last_chng,snmp_comn,poll_port,ip,note from devices_$hostname order by snmp_comn desc, last_stat asc");

	$sql_device_list->execute();
	$start_polling->up();

	while (@device_info = $sql_device_list->fetchrow_array()) {
		$queue_limit->down();
		$device_unknown->enqueue(\@device_info); # push the last status onto the queue
	}
	$device_unknown->enqueue('END');

	$stop_polling->up();

	$DB->disconnect;

	$status_message->enqueue("Stopped device reader.\n") if ($debug);

}

# Start device writer
sub device_writer () { # write the current status of all devices to the database
	# The DBI module is restricted to this subroutine to reduce memory utilization in the overall process
	require DBI;
	import DBI;

	undef($add);
	undef($drop);
	undef($listadd);
	undef($listdrop);
	undef($nbiadd);
	undef($nbidrop);
	undef($customer);
	undef($hostupdate);
	undef($hostdelete);
	undef($status);
	undef($backup);
	undef($restore);

	my $device_ref;
	my @device_info;

	$status_message->enqueue("Starting device writer.\n") if ($debug);

	# Open Database
	my $DB = DBI->connect("DBI:mysql:database=moto_poll;host=$mysql_host","$mysql_user","$mysql_pass") || &log_exit("Failed to connect to database: $DBI::errstr\n");

	# Prepare database commands
	my $sql_device_update = $DB->prepare("update devices_$hostname set last_poll=?,last_stat=?,last_chng=? where ip=?");

	while ($device_ref = $device_known->dequeue()) { # grab the next entry from the queue
		last if ($device_ref eq 'END');
		@device_info = @$device_ref;
		$sql_device_update->execute(@device_info);
	}

	$DB->disconnect;

	$status_message->enqueue("Stopped device writer.\n") if ($debug);

}

# Start AP reader CURRENTLY UNUSED
sub ap_reader () {
	# The DBI module is restricted to this subroutine to reduce memory utilization in the overall process
	require DBI;
	import DBI;

	undef($add);
	undef($drop);
	undef($listadd);
	undef($listdrop);
	undef($nbiadd);
	undef($nbidrop);
	undef($customer);
	undef($hostupdate);
	undef($hostdelete);
	undef($status);
	undef($backup);
	undef($restore);

	my $ap_ref;
	my @ap_info;

	$status_message->enqueue("Starting AP reader.\n") if ($debug);

	# Open Database
	my $DB = DBI->connect("DBI:mysql:database=moto_poll;host=$mysql_host","$mysql_user","$mysql_pass") || &log_exit("Failed to connect to database: $DBI::errstr\n");

	# Prepare database commands
	my $sql_ap_list = $DB->prepare("select sql_buffer_result last_poll,last_stat,last_chng,polled,switch,name from aps_$hostname order by switch asc");

	$sql_ap_list->execute();

	while (@ap_info = $sql_ap_list->fetchrow_array()) {
		$ap_known->enqueue(\@ap_info);
	}
	$ap_known->enqueue('END');

	$sql_ap_list = undef();

	$DB->disconnect;

	$status_message->enqueue("Stopped AP reader.\n") if ($debug);
}


# Start AP writer
sub ap_writer () { # Update the status of APs in the database
	# The DBI module is restricted to this subroutine to reduce memory utilization in the overall process
	require DBI;
	import DBI;

	undef($add);
	undef($drop);
	undef($listadd);
	undef($listdrop);
	undef($nbiadd);
	undef($nbidrop);
	undef($customer);
	undef($hostupdate);
	undef($hostdelete);
	undef($status);
	undef($backup);
	undef($restore);

	my $ap_ref;
	my @ap_info;
	my $curr;

	$status_message->enqueue("Starting AP writer.\n") if ($debug);

	# Open Database
	my $DB = DBI->connect("DBI:mysql:database=moto_poll;host=$mysql_host","$mysql_user","$mysql_pass") || &log_exit("Failed to connect to database: $DBI::errstr\n");

	# Prepare database commands
	my $sql_ap_old_stat = $DB->prepare("select last_stat from aps_$hostname where switch=? and name=?");
	my $sql_ap_add = $DB->prepare("insert into aps_$hostname (last_stat,polled,switch,name) values (?,?,?,?)");
	my $sql_ap_update = $DB->prepare("update aps_$hostname set last_stat=?,polled=? where switch=? and name=?");

	while ($ap_ref = $ap_known->dequeue()) { # grab the next entry from the queue
		last if ($ap_ref eq 'END');
		@ap_info = @$ap_ref;
		my ($stat, $switch, $name) = @ap_info;
		if ($name eq 'SWITCH') { # this is a meta-flag indicating a switch device, not an AP
			if ($stat) { # polling of the switch is complete, delete any unpolled APs from the database, to reflect the current AP inventory
				$DB->do("delete from aps_$hostname where switch='$switch' and polled=0");
			} else { # set the polled flag for all APs on this switch to 0, so we can keep track of which ones are still in inventory after each poll
				$DB->do("update aps_$hostname set polled=0 where switch='$switch'");
			}
		} else {
			$curr = strftime("%F %T", localtime);
			$sql_ap_old_stat->execute($switch,$name);
			my $last_stat = $sql_ap_old_stat->fetchrow_array();
			if ($last_stat) { # AP already has a status
				if ($last_stat eq 'up' and $stat eq 'down') { # status has changed from up to down, send a trap
					my $last_chng = $curr;
					&send_trap($name,"AP unadopt. $name at $curr from $switch.","");
					&log_only("AP unadopt. $name at $curr from $switch.");
				} elsif ($last_stat eq 'down' and $stat eq 'up') { # status has changed from down to up, send a trap
					my $last_chng = $curr;
					&send_trap($name,"AP adopt. $name at $curr from $switch.","");
					&log_only("AP adopt. $name at $curr from $switch.");
				} elsif ($continuous and $stat eq 'down') { # continuous down notification flag is set, always send down traps
					&send_trap($name,"AP unadopt. $name at $curr from $switch.","");
				}
				$sql_ap_update->execute($stat,1,$switch,$name); # update AP status in the database, and mark it as polled
			} else { # a new AP, only send a trap if its down
				if ($stat eq 'down') {
					&send_trap($name,"AP unadopt. $name at $curr from $switch.","");
					&log_only("AP unadopt. $name at $curr from $switch.");
				}
				$sql_ap_add->execute($stat,1,$switch,$name); # add the new AP to the database
			}
		}
	}

	$sql_ap_old_stat = undef();
	$sql_ap_add = undef();
	$sql_ap_update = undef();

	$DB->disconnect;

	$status_message->enqueue("Stopped AP writer.\n") if ($debug);
}

# Polling control master
sub poll_master () {

	undef($add);
	undef($drop);
	undef($listadd);
	undef($listdrop);
	undef($nbiadd);
	undef($nbidrop);
	undef($customer);
	undef($hostupdate);
	undef($hostdelete);
	undef($status);
	undef($backup);
	undef($restore);

	$start_polling->down();

	my $pending = $device_unknown->pending();
	my $poller;
	my $snmp;
	my @pollers;
	my @snmps;
	my $poller_limit = int($device_total / 30)+1;
	my $snmp_limit = int($switch_total / 20)+1;
	my $count;
	my $device_ref;
	my @device_info;
	my $threads;

	if ($poller_limit > $global_thread_limit) {
		$poller_limit = $global_thread_limit;
	}
	&log_only("Starting $poller_limit ping pollers for $device_total devices.");

	if ($snmp_limit > $global_thread_limit) {
		$snmp_limit = $global_thread_limit;
	}
	&log_only("Starting $snmp_limit SNMP pollers for $switch_total RFS switches.");

	while ($pending == 0) { # wait until there are devices in the polling queue before starting threads, to avoid a undef value error.
		$pending = $device_unknown->pending();
	}

	for (my $count=0; $count < $snmp_limit; $count++) { # start up the SNMP pollers, and add the thread IDs to the list
		$snmp = threads->create(\&snmp_slave,$count);
		push(@snmps,$snmp);
	}

	for (my $count=0; $count < $poller_limit; $count++) { # start the ping pollers and add the thread IDs to the list
		$poller = threads->create(\&ping_slave,$count);
		push(@pollers,$poller);
	}

	$stop_polling->down(); # Wait for the database reader to signal that all devices are in queue.

	for (my $count=0; $count < $poller_limit; $count++) { # add an 'END' flag to the queue for each ping poller, to tell it to shut down
		$device_unknown->enqueue('END');
	}

	foreach $threads (@pollers) { # wait for all the ping threads to close
		$threads->join();
	}

	for (my $count=0; $count < $snmp_limit; $count++) { # add an 'END' flag to the queue for each SNMP poller, to tell it to shut down
		$switch_unknown->enqueue('END');
	}

	foreach $threads (@snmps) { # wait for all SNMP threads to close
		$threads->join();
	}

	$device_known->enqueue('END'); # Signal the device writer thread to close
	$ap_known->enqueue('END'); # Signal the AP writer thread to close
}

# Ping Poller slave
sub ping_slave () {

	# Only import the ping code to these processes, to reduce memory use
	require Net::Ping; # allow us to ping devices internally
	import Net::Ping;

	undef($add);
	undef($drop);
	undef($listadd);
	undef($listdrop);
	undef($nbiadd);
	undef($nbidrop);
	undef($customer);
	undef($hostupdate);
	undef($hostdelete);
	undef($status);
	undef($backup);
	undef($restore);
	undef($version);

	my $id = $_[0];

	my $device_ref;
	my @device_info;
	my $ret;
	my $stat;
	my $curr;
	my $ping_stat;

	$status_message->enqueue("Starting ping poller #$id.\n") if ($debug);

	while ($device_ref = $device_unknown->dequeue()) { # grab the next device from the queue

		$queue_limit->up();

		last if ($device_ref eq 'END');
		my ($last_poll, $last_stat, $last_chng, $community, $port, $ip, $note) = @$device_ref;
		$stat = 'down';

		if ($port == 0) { # port 0 indicates an ICMP ping, any other number designates the TCP port to ping
			$status_message->enqueue("Ping poller #$id: testing: $ip, ICMP ping\n") if ($debug);
			$ping_stat = Net::Ping->new('icmp',1)
		} else {
			$status_message->enqueue("Ping poller #$id: testing: $ip, port $port\n") if ($debug);
			$ping_stat = Net::Ping->new('tcp',1);
			$ping_stat->port_number($port);
		}

		# Ping the device, first successful ping ends the session, and sets the status to up. Each successive ping attempt is made with a longer timeout.
		if (my $ret = $ping_stat->ping($ip)) {
			$stat = 'up';
#		} elsif ($ret = $ping_stat->ping($ip)) {
#			$stat = 'up';
		} elsif ($ret = $ping_stat->ping($ip,3)) {
			$stat = 'up';
		} elsif ($ret = $ping_stat->ping($ip,5)) {
			$stat = 'up';
		}
		$ping_stat->close(); # close the current ping session

		$curr = strftime("%F %T", localtime);

		if ($last_stat eq 'up' and $stat eq 'down') { # status has changed from up to down, send a trap
			$last_chng = $curr;
			&send_trap($ip,"Node failure. $ip, port $port at $curr from $hostname.",$note);
			&log_only("Node failure. $ip, port $port");
		} elsif ($last_stat eq 'down' and $stat eq 'up') { # status has changed from down to up, send a trap
			$last_chng = $curr;
			&send_trap($ip,"Node clear. $ip, port $port at $curr from $hostname.",$note);
			&log_only("Node clear. $ip, port $port");
		} elsif ($continuous and $stat eq 'down') { # continuous reporting flag is set, send all down traps
			&send_trap($ip,"Node failure. $ip, port $port at $curr from $hostname.",$note);
		}

		@device_info=($curr, $stat, $last_chng, $ip);
		$device_known->enqueue(\@device_info); # push the current status onto the known status queue

		if (defined($community)) { # if the community variable is set, this is a Wing switch and an SNMP poll of AP status should be performed
			if ($stat eq 'up') { # but only if the switch is currently online
				$status_message->enqueue("Ping poller #$id: switch $ip is up, polling APs\n") if ($debug);
				$snmp_queue_limit->down();
				@device_info=($curr, $stat, $last_chng, $community, $port, $ip, $note);
				$switch_unknown->enqueue(\@device_info);
			}
		}
	}

	$status_message->enqueue("Stopping ping poller #$id.\n") if ($debug);
}

# SNMP Poller slave
sub snmp_slave () {

	undef($add);
	undef($drop);
	undef($listadd);
	undef($listdrop);
	undef($nbiadd);
	undef($nbidrop);
	undef($customer);
	undef($hostupdate);
	undef($hostdelete);
	undef($status);
	undef($backup);
	undef($restore);
	undef($version);

	my $id = $_[0];

	my $switch_ref;
	my @switch_info;
	my $ret;
	my $stat;
	my $curr;

	$status_message->enqueue("Starting SNMP poller #$id.\n") if ($debug);

	while ($switch_ref = $switch_unknown->dequeue()) { # Grab the next switch from the queue

		$snmp_queue_limit->up();

		last if ($switch_ref eq 'END');
		my ($last_poll, $last_stat, $last_chng, $community, $port, $ip, $note) = @$switch_ref;
		$status_message->enqueue("SNMP poller #$id: testing: $ip\n") if ($debug);

		if (defined($community)) {
			if ($last_stat eq 'up') {
				my $snmp_session;
				my $error;
				my @columns=('1.3.6.1.4.1.388.50.1.4.1.2.1.2','1.3.6.1.4.1.388.50.1.4.1.2.1.1','1.3.6.1.4.1.388.50.1.4.1.2.1.7');
				# Pulling three columns from the AP status table on the Wing controllers
				# OID.2 = AP Name, OID.1 = AP MAC address, and OID.7 = AP Status

				($snmp_session, $error) = Net::SNMP->session(
					-hostname => $ip,
					-community => $community,
					-timeout => 5,
					-version => '2c',
					-translate => TRANSLATE_NONE,
					);

				if (!defined($snmp_session)) { # Unable to open SNMP session to the switch, send an error message
					&log_only("ERROR: $error.");
					$status_message->enqueue("ERROR: $error.\n") if ($debug);
				} else {
					my $result=$snmp_session->get_entries( -columns => \@columns );
					if (!defined($result)) {
						&send_trap($ip,"SNMP query failed on $ip from $hostname.",$note);
						&log_only("SNMP poll failed! Error: " .  $snmp_session->error());
					} else {
						my %ret_values=%{$result};
						my $oid;
						my $type;
						my $object;
						my $value;
						my %ap_name;
						my %ap_mac;
						my %ap_status;

						my @ap_info=(0, $ip, 'SWITCH'); # for each switch, first toggle the 'polled' status of all attached APs
						$ap_known->enqueue(\@ap_info);

						# AP information is returned in a semi-random order, need to break it down into matched hashes
						while (($oid,$value) = each(%ret_values)) {
							$type=substr($oid,29,1); # The 29th character in the OID is the type
							$object=substr($oid,31); # Everything after the 30th character is an ID, unique to each AP on the switch, use this to index the hashes
							if ( $type == 2 ) {
								$ap_name{$object}=$value;
							} elsif ( $type == 1 ) {
								$ap_mac{$object}=$value;
							} elsif ( $type == 7 ) {
								$ap_status{$object}=$value;
							} else {
								&log_only("Error: $ip, unknown OID type!");
							}
						}
						while (($object,$value) = each(%ap_name)) { # for each entry in the name hash, get the matching status and push them into the status queue
							if ($ap_status{$object} == 1) {
								@ap_info=('up', $ip, $ap_name{$object});
								$ap_known->enqueue(\@ap_info);
							} else {
								@ap_info=('down', $ip, $ap_name{$object});
								$ap_known->enqueue(\@ap_info);
							}
						}
						@ap_info=(1, $ip, 'SWITCH'); # polling of the switch is complete signal that unpolled APs can be removed from the database
						$ap_known->enqueue(\@ap_info);
					}
				}
				$snmp_session->close();
			}
		}
	}

	$status_message->enqueue("Stopping SNMP Poller #$id.\n") if ($debug);
}

# Subroutine to show help message
sub show_help () {
	$status_message->enqueue("
Motorola Ping Poller v$version

MOTO_POLL [<command> <argument>]

MOTO_POLL accepts a single command to perform special operations. Valid commands and their arguments are:
	-add/drop <IP> : add or drop a single IP from the poll list.
	-listadd/listdrop <file> : add or drop a list of IPs from a file.
	-snmpon <IP> -community <name> : activate SNMP polling of a single IP, with the supplied community string.
	-snmpoff <IP> : deactivate SNMP polling of a single IP.
	-listsnmpon <file> -community <name> : activate SNMP polling of devices listed in a file, with the supplied community string.
	-listsnmpoff <file> : deactivate SNMP polling of all devices listed in a file.
	-tcpon <IP> -port <#> : activate TCP polling of a single IP, with the supplied port number.
	-tcpoff <IP> : deactivate TCP polling of a single IP.
	-listtcpon <file> -port <#> : activate TCP polling of devices listed in a file, with the supplied port number.
	-listtcpoff <file> : deactivate TCP polling of all devices listed in a file.
	-nbiadd/nbidrop <IP> : add or drop a NBI destination.
	-customer <name> : set the snmp community name for all traps.
	-hostupdate <name> : update the selected hostname to the current hostname, useful if the host is renamed.
	-hostdelete <name> : delete the selected hostname entry.
	-noteadd/notedrop <file> : add or drop notes from devices listed in a file:
		- when adding notes, the file should have one device per line, in the following layout:
			<device IP><tab or space>The text of the note (128 chaacters max).
		- when deleting notes, no special formatting is needed, juat a list of devices.
	-status [<search string>|devices|aps|resend|poller] : perform status checks:
		: <search string> : check the status of device(s), use '%' as a wildcard instead of '*'.
		: devices : display the status of all devices, sorted by the last status change date.
		: aps : display the status of all Aps, sorted by switch.
		: resend : resend the current status of all devices and APs via SNMP traps.
		: poller : display the status of the poller process.
		: notes : display all devices with notes.
	-backup <file> : save the poller configuration to a file.
	-restore <file> : load the poller config from a saved backup. WARNING: this will overwrite the current config!

Execute without a command to perform poll of the IP list.

During a poll, MOTO_POLL also accepts options to modify it's behavior:
	--continuous : cause MOTO_POLL to send a trap for all 'down' devices on every polling cycle.
	--debug : cause MOTO_POLL to print additional debugging messages to standard-out.
");
}

# This function generates the snmptrap. It takes two variables, the IP of the
# referenced device, and the trap text.
sub send_trap () {
	my $dev = $_[0];
	my $message = $_[1];
	my $note = $_[2];
	my @trap = ();
	my $timeticks = time;
	my $enterprise = '1.3.6.1.4.1.161.3.10.104.3';

	$note = "" unless ($note);

	push @trap,("1.3.6.1.2.1.1.3.0", TIMETICKS, $timeticks);
	push @trap,("1.3.6.1.6.3.1.1.4.1.0", OBJECT_IDENTIFIER, $enterprise);
	push @trap,("1.1.0", OCTET_STRING, $dev);
	push @trap,("1.2.0", OCTET_STRING, $message);
	push @trap,("1.3.0", OCTET_STRING, $dev);
	push @trap,("1.4.0", OCTET_STRING, $dev);
	push @trap,("1.5.0", OCTET_STRING, $note);
	push @trap,("1.6.0", OCTET_STRING, "");
	push @trap,("1.7.0", OCTET_STRING, "");
	push @trap,("1.8.0", OCTET_STRING, $dev);
	push @trap,("1.9.0", OCTET_STRING, "");
	push @trap,("1.10.0", OCTET_STRING, "MOTO_POLL");


	$trap_limit->down(); # grab a snmptrap semaphore

	foreach my $nbi (@NBIS) { # Send a trap to each NBI configured
		my ($trap_session, $error) = Net::SNMP->session(
									-hostname => $nbi,
									-community => $CUSTOMER,
									-version => '2c',
									-port => '162',
									);

		if (!defined($trap_session)) {
			$status_message->enqueue("Trap failed: $error \n") if ($debug);
			&log_only("Trap failed: $error \n");
		} else {
			my $trap_result = $trap_session->snmpv2_trap( -varbindlist => \@trap );
		}

		$trap_session->close();
	}

	$trap_limit->up(); # release the snmptrap semaphore
}

# This function generates the heartbeat. It generates a trap to the local trap forwarder
sub send_heartbeat () {
	my $run_time=$_[0];
	my @trap = ();
	my $timeticks = time;
	my $enterprise = '1.3.6.1.4.1.161.3.10.104.3';

	push @trap,("1.3.6.1.2.1.1.3.0", TIMETICKS, $timeticks);
	push @trap,("1.3.6.1.6.3.1.1.4.1.0", OBJECT_IDENTIFIER, $enterprise);
	push @trap,("1.1.0", OCTET_STRING, $hostname) if ($script ne 'MOTO_POLL');
	push @trap,("1.2.0", OCTET_STRING, "Poller is alive at $finish_time. Poll time: $run_time seconds.");
	push @trap,("1.3.0", OCTET_STRING, $hostname);
	push @trap,("1.4.0", OCTET_STRING, $hostname);
	push @trap,("1.5.0", OCTET_STRING, "$finish_time");
	push @trap,("1.6.0", OCTET_STRING, "$run_time");
	push @trap,("1.7.0", OCTET_STRING, "");
	push @trap,("1.8.0", OCTET_STRING, $hostname);
	push @trap,("1.9.0", OCTET_STRING, "");
	push @trap,("1.10.0", OCTET_STRING, "MOTO_POLL");


	$trap_limit->down(); # grab a snmptrap semaphore

	my ($trap_session, $error) = Net::SNMP->session(
								-hostname => 'localhost',
								-community => $CUSTOMER,
								-version => '2c',
								-port => '162',
								);

	if (!defined($trap_session)) {
		$status_message->enqueue("Trap failed: $error \n") if ($debug);
		&log_only("Trap failed: $error \n");
	} else {
		my $trap_result = $trap_session->snmpv2_trap( -varbindlist => \@trap );
	}

	$trap_session->close();

	$trap_limit->up(); # release the snmptrap semaphore
}

# Send message to syslog
sub log_only () {
	require Sys::Syslog; # allow logging to the syslog
	import Sys::Syslog;

	# Open the syslog for writing
	openlog($script, '', 'LOG_USER');

	my $message = $_[0];
	syslog('LOG_INFO',$message);
	$status_message->enqueue("$message\n");
}

# Send message to syslog and die immediately
sub log_exit () {
	require Sys::Syslog; # allow logging to the syslog
	import Sys::Syslog;

	# Open the syslog for writing
	openlog($script, '', 'LOG_USER');

	my $message = $_[0];
	syslog('LOG_WARNING',$message);
	threads->exit($message);
}

# Print messages to standard out
sub print_message () {
	while (my $message = $status_message->dequeue()) {
		last if ( $message eq 'END');
		print($message);
	}
}

sub get_opts () {
	require Getopt::Long; # command line options handling
	import Getopt::Long;

	GetOptions(
		'add=s'			=> \$add,
		'drop=s'		=> \$drop,
		'listadd=s'		=> \$listadd,
		'listdrop=s'	=> \$listdrop,
		'nbiadd=s'		=> \$nbiadd,
		'nbidrop=s'		=> \$nbidrop,
		'snmpon=s'		=> \$snmpon,
		'snmpoff=s'		=> \$snmpoff,
		'listsnmpon=s'	=> \$listsnmpon,
		'listsnmpoff=s'	=> \$listsnmpoff,
		'tcpon=s'		=> \$tcpon,
		'tcpoff=s'		=> \$tcpoff,
		'listtcpon=s'	=> \$listtcpon,
		'listtcpoff=s'	=> \$listtcpoff,
		'community=s'	=> \$snmpcom,
		'port=i'		=> \$pingport,
		'customer=s'	=> \$customer,
		'hostupdate=s'	=> \$hostupdate,
		'hostdelete=s'	=> \$hostdelete,
		'noteadd=s'		=> \$noteadd,
		'notedrop=s'	=> \$notedrop,
		'status=s'		=> \$status,
		'backup=s'		=> \$backup,
		'restore=s'		=> \$restore,
		'debug'			=> \$debug,
		'continuous'		=> \$continuous,
		) or &show_help();
}
