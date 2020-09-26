{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_lazy_potential_analysis (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/sara/lazy-potential-analysis/.stack-work/install/x86_64-linux/63a2c4fdfb97dcfef108e1193db62f3495d2a8c30aaee6fa67f08209d41c689e/8.4.3/bin"
libdir     = "/home/sara/lazy-potential-analysis/.stack-work/install/x86_64-linux/63a2c4fdfb97dcfef108e1193db62f3495d2a8c30aaee6fa67f08209d41c689e/8.4.3/lib/x86_64-linux-ghc-8.4.3/lazy-potential-analysis-0.1-Gy75CRydVkPLOkmamJyiuD-runanalysis"
dynlibdir  = "/home/sara/lazy-potential-analysis/.stack-work/install/x86_64-linux/63a2c4fdfb97dcfef108e1193db62f3495d2a8c30aaee6fa67f08209d41c689e/8.4.3/lib/x86_64-linux-ghc-8.4.3"
datadir    = "/home/sara/lazy-potential-analysis/.stack-work/install/x86_64-linux/63a2c4fdfb97dcfef108e1193db62f3495d2a8c30aaee6fa67f08209d41c689e/8.4.3/share/x86_64-linux-ghc-8.4.3/lazy-potential-analysis-0.1"
libexecdir = "/home/sara/lazy-potential-analysis/.stack-work/install/x86_64-linux/63a2c4fdfb97dcfef108e1193db62f3495d2a8c30aaee6fa67f08209d41c689e/8.4.3/libexec/x86_64-linux-ghc-8.4.3/lazy-potential-analysis-0.1"
sysconfdir = "/home/sara/lazy-potential-analysis/.stack-work/install/x86_64-linux/63a2c4fdfb97dcfef108e1193db62f3495d2a8c30aaee6fa67f08209d41c689e/8.4.3/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "lazy_potential_analysis_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "lazy_potential_analysis_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "lazy_potential_analysis_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "lazy_potential_analysis_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "lazy_potential_analysis_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "lazy_potential_analysis_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
