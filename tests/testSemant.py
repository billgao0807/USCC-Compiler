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

__unittest = True

class SemantTests(unittest.TestCase):
	
	def setUp(self):
		self.maxDiff = None
		if not os.path.isfile(uscc):
			raise Exception("Can't run without uscc")

	def checkAST(self, fileName):
		# read in expected
		expectFile = open("expected/" + fileName + ".semant.ast", "r")
		expectedStr = expectFile.read();
		expectFile.close()
		try:
			resultStr = subprocess.check_output([uscc, "-a", "-l", fileName + ".usc"], stderr=subprocess.STDOUT)
			self.assertMultiLineEqual(expectedStr, resultStr)
		except subprocess.CalledProcessError as e:
			self.fail("\n" + e.output)
	
	def checkError(self, fileName):
		# read in expected
		expectFile = open("expected/" + fileName + ".semant.err", "r")
		expectedStr = expectFile.read()
		expectFile.close()
		try:
			resultStr = subprocess.check_output([uscc, "-a", "-l", fileName + ".usc"], stderr=subprocess.STDOUT)
			self.assertMultiLineEqual(expectedStr, resultStr)
		except subprocess.CalledProcessError as e:
			outputStr = e.output
			outputStr = outputStr.replace('\r\n','\n')
			self.assertMultiLineEqual(expectedStr, outputStr)
			
	def test_Sem_001(self):
		self.checkAST("test001")
	
	def test_Sem_006(self):
		self.checkAST("test006")
	
	def test_Sem_007(self):
		self.checkAST("test007")

	def test_Sem_015(self):
		self.checkAST("test015")

	def test_Sem_016(self):
		self.checkAST("test016")

	def test_Sem_quicksort(self):
		self.checkAST("quicksort")
	
	def test_Sem_semant01(self):
		self.checkAST("semant01")
		
	def test_Sem_semant02(self):
		self.checkAST("semant02")
		
	def test_Sem_emit01(self):
		self.checkAST("emit01")
		
	def test_Sem_emit02(self):
		self.checkAST("emit02")
		
	def test_Sem_emit03(self):
		self.checkAST("emit03")

	def test_Sem_emit04(self):
		self.checkAST("emit04")
		
	def test_Sem_emit05(self):
		self.checkAST("emit05")
		
	def test_Sem_emit06(self):
		self.checkAST("emit06")
		
	def test_Sem_emit07(self):
		self.checkAST("emit07")
	
	def test_Sem_emit08(self):
		self.checkAST("emit08")
			
	def test_Sem_emit09(self):
		self.checkAST("emit09")
		
	def test_Sem_emit10(self):
		self.checkAST("emit10")
		
	def test_Sem_emit11(self):
		self.checkAST("emit11")
		
	def test_Sem_emit12(self):
		self.checkAST("emit12")
		
	def test_SemErr_semant01e(self):
		self.checkError("semant01e")
	
	def test_SemErr_semant02e(self):
		self.checkError("semant02e")
		
	def test_SemErr_semant03e(self):
		self.checkError("semant03e")
		
	def test_SemErr_semant04e(self):
		self.checkError("semant04e")
		
	def test_SemErr_semant05e(self):
		self.checkError("semant05e")
	
	def test_SemErr_semant06e(self):
		self.checkError("semant06e")
		
	def test_SemErr_semant07e(self):
		self.checkError("semant07e")
		
	def test_SemErr_semant08e(self):
		self.checkError("semant08e")
		
	def test_SemErr_semant09e(self):
		self.checkError("semant09e")
		
	def test_SemErr_semant10e(self):
		self.checkError("semant10e")
		
	def test_SemErr_semant11e(self):
		self.checkError("semant11e")
		
	def test_SemErr_semant12e(self):
		self.checkError("semant12e")
		
	def test_SemErr_002(self):
		self.checkError("test002")
		
	def test_SemErr_003(self):
		self.checkError("test003")
		
	def test_SemErr_004(self):
		self.checkError("test004")
	
	def test_SemErr_005(self):
		self.checkError("test005")
	
	def test_SemErr_008(self):
		self.checkError("test008")
		
	def test_SemErr_009(self):
		self.checkError("test009")
		
	def test_SemErr_010(self):
		self.checkError("test010")
		
	def test_SemErr_011(self):
		self.checkError("test011")
		
	def test_SemErr_012(self):
		self.checkError("test012")
	
	def test_SemErr_013(self):
		self.checkError("test013")
	
	def test_SemErr_014(self):
		self.checkError("test014")
if __name__ == '__main__':
	unittest.main(verbosity=2)
