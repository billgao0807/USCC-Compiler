#---------------------------------------------------------
# Copyright (c) 2014, Sanjay Madhav
# All rights reserved.
#
# This file is distributed under the BSD license.
# See LICENSE.TXT for details.
#---------------------------------------------------------
import subprocess
import glob
import os
extension = ".output"
uscc = "../bin/uscc"
lli = "../../bin/lli"
for f in glob.iglob("*.usc"):
	file = f.split(".")
	if not os.path.isfile("expected/" + file[0] + extension):
		subprocess.call([uscc, file[0] + "." + file[1]])
		outfile = open("expected/" + file[0] + extension, "w")
		subprocess.call([lli, file[0] + ".bc"], stdout=outfile)
		outfile.close()
		if os.path.getsize("expected/" + file[0] + extension) == 0:
			os.remove("expected/" + file[0] + extension)
