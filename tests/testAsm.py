#---------------------------------------------------------
# Copyright (c) 2014, Sanjay Madhav
# All rights reserved.
#
# This file is distributed under the BSD license.
# See LICENSE.TXT for details.
#---------------------------------------------------------
import subprocess
import os
import sys

import unittest
uscc = "../bin/uscc"
lli = "../../bin/lli"
gcc = "gcc"

__unittest = True

class AsmTests(unittest.TestCase):
	
	def setUp(self):
		self.maxDiff = None
		if not os.path.isfile(uscc):
			raise Exception("Can't run without uscc")

	def checkEmit(self, fileName):
		# read in expected
		expectFile = open("expected/" + fileName + ".output", "r")
		expectedStr = expectFile.read()
		expectFile.close()
		# first compile to asm via uscc
		try:
			resultStr = subprocess.check_output([uscc, "-s", fileName + ".usc"], stderr=subprocess.STDOUT)
		except subprocess.CalledProcessError as e:
			self.fail("\n" + e.output)
		
		# now aseemble into machine code (via gcc)
		try:
			resultStr = subprocess.check_output([gcc, fileName + ".s", "-o", fileName + ".out"], stderr=subprocess.STDOUT)
		except subprocess.CalledProcessError as e:
			self.fail("\n" + e.output)

		# now try running and compare output
		try:
			resultStr = subprocess.check_output(["./" + fileName + ".out"], stderr=subprocess.STDOUT)
			self.assertMultiLineEqual(expectedStr, resultStr)
		except subprocess.CalledProcessError as e:
			self.fail("\n" + e.output)
			
	def test_Asm_emit02(self):
		self.checkEmit("emit02")
		
	def test_Asm_emit03(self):
		self.checkEmit("emit03")
		
	def test_Asm_emit04(self):
		self.checkEmit("emit04")
		
	def test_Asm_emit05(self):
		self.checkEmit("emit05")
		
	def test_Asm_emit06(self):
		self.checkEmit("emit06")
		
	def test_Asm_emit07(self):
		self.checkEmit("emit07")
		
	def test_Asm_emit08(self):
		self.checkEmit("emit08")
		
	def test_Asm_emit09(self):
		self.checkEmit("emit09")
		
	def test_Asm_emit10(self):
		self.checkEmit("emit10")
		
	def test_Asm_emit11(self):
		self.checkEmit("emit11")
		
	def test_Asm_emit12(self):
		self.checkEmit("emit12")
		
	def test_Asm_quicksort(self):
		self.checkEmit("quicksort")
		
	def test_Asm_015(self):
		self.checkEmit("test015")
		
	def test_Asm_016(self):
		self.checkEmit("test016")
		
	def test_Asm_opt01(self):
		self.checkEmit("opt01")
		
	def test_Asm_opt02(self):
		self.checkEmit("opt02")
		
	def test_Asm_opt03(self):
		self.checkEmit("opt03")
		
	def test_Asm_opt04(self):
		self.checkEmit("opt04")	
		
	def test_Asm_opt05(self):
		self.checkEmit("opt05")
		
	def test_Asm_opt06(self):
		self.checkEmit("opt06")
		
	def test_Asm_opt07(self):
		self.checkEmit("opt07")
if __name__ == '__main__':
	unittest.main(verbosity=2)
