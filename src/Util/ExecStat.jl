  module ExecStat 


    using MetaModelica
    #= ExportAll is not good practice but it makes it so that we do not have to write export after each function :( =#
    using ExportAll

        import ClockIndexes
        import Error
        import GC
        import Global
        import Flags
        import System
        import StringUtil

        function execStatReset()  
              System.realtimeTick(ClockIndexes.RT_CLOCK_EXECSTAT)
              System.realtimeTick(ClockIndexes.RT_CLOCK_EXECSTAT_CUMULATIVE)
              setGlobalRoot(Global.gcProfilingIndex, GC.getProfStats())
        end

         #= Prints an execution stat on the format:
          *** %name% -> time: %time%, memory %memory%
          Where you provide name, and time is the time since the last call using this
          index (the clock is reset after each call). The memory is the total memory
          consumed by the compiler at this point in time.
           =#
        function execStat(name::String)  
              local t::ModelicaReal
              local total::ModelicaReal
              local timeStr::String
              local totalTimeStr::String
              local gcStr::String
              local memory::ModelicaInteger
              local oldMemory::ModelicaInteger
              local heapsize_full::ModelicaInteger
              local free_bytes_full::ModelicaInteger
              local since::ModelicaInteger
              local before::ModelicaInteger
              local stats::GC.ProfStats
              local oldStats::GC.ProfStats

              if Flags.isSet(Flags.EXEC_STAT)
                for i in if Flags.isSet(Flags.EXEC_STAT_EXTRA_GC)
                       list(1, 2)
                     else
                       list(1)
                     end
                  if i == 2
                    GC.gcollect()
                  end
                  stats = GC.getProfStats()
                  @match GC.PROFSTATS(bytes_allocd_since_gc = since, allocd_bytes_before_gc = before, heapsize_full = heapsize_full, free_bytes_full = free_bytes_full) = stats
                  memory = since + before
                  oldStats = getGlobalRoot(Global.gcProfilingIndex)
                  @match GC.PROFSTATS(bytes_allocd_since_gc = since, allocd_bytes_before_gc = before) = oldStats
                  oldMemory = since + before
                  t = System.realtimeTock(ClockIndexes.RT_CLOCK_EXECSTAT)
                  total = System.realtimeTock(ClockIndexes.RT_CLOCK_EXECSTAT_CUMULATIVE)
                  timeStr = System.snprintff("%.4g", 20, t)
                  totalTimeStr = System.snprintff("%.4g", 20, total)
                  if Flags.isSet(Flags.GC_PROF)
                    gcStr = GC.profStatsStr(stats, head = "", delimiter = " / ")
                    Error.addMessage(Error.EXEC_STAT_GC, list(name + (if i == 2
                          " GC"
                        else
                          ""
                        end), timeStr, totalTimeStr, gcStr))
                  else
                    Error.addMessage(Error.EXEC_STAT, list(name + (if i == 2
                          " GC"
                        else
                          ""
                        end), timeStr, totalTimeStr, StringUtil.bytesToReadableUnit(memory - oldMemory, maxSizeInUnit = 500, significantDigits = 4), StringUtil.bytesToReadableUnit(memory, maxSizeInUnit = 500, significantDigits = 4), StringUtil.bytesToReadableUnit(free_bytes_full, maxSizeInUnit = 500, significantDigits = 4), StringUtil.bytesToReadableUnit(heapsize_full, maxSizeInUnit = 500, significantDigits = 4)))
                  end
                  System.realtimeTick(ClockIndexes.RT_CLOCK_EXECSTAT)
                  setGlobalRoot(Global.gcProfilingIndex, stats)
                end
              end
        end

    #= So that we can use wildcard imports and named imports when they do occur. Not good Julia practice =#
    @exportAll()
  end