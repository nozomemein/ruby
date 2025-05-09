# frozen_string_literal: false
require 'test/unit'

require 'tmpdir'
require 'fileutils'

class TestDir < Test::Unit::TestCase

  def setup
    @verbose = $VERBOSE
    @root = File.realpath(Dir.mktmpdir('__test_dir__'))
    @nodir = File.join(@root, "dummy")
    @dirs = []
    for i in "a".."z"
      if i.ord % 2 == 0
        FileUtils.touch(File.join(@root, i))
      else
        FileUtils.mkdir(File.join(@root, i))
        @dirs << File.join(i, "")
      end
    end
    @envs = nil
  end

  def teardown
    $VERBOSE = @verbose
    FileUtils.remove_entry_secure @root if File.directory?(@root)
    ENV.update(@envs) if @envs
  end

  def setup_envs(envs = %w"HOME LOGDIR")
    @envs ||= {}
    envs.each do |e, v|
      @envs[e] = ENV.delete(e)
      ENV[e] = v if v
    end
  end

  def test_seek
    dir = Dir.open(@root)
    begin
      cache = []
      loop do
        pos = dir.tell
        break unless name = dir.read
        cache << [pos, name]
      end
      for x,y in cache.sort_by {|z| z[0] % 3 } # shuffle
        dir.seek(x)
        assert_equal(y, dir.read)
      end
    ensure
      dir.close
    end
  end

  def test_nodir
    assert_raise(Errno::ENOENT) { Dir.open(@nodir) }
  end

  def test_inspect
    d = Dir.open(@root)
    assert_match(/^#<Dir:#{ Regexp.quote(@root) }>$/, d.inspect)
    assert_match(/^#<Dir:.*>$/, Dir.allocate.inspect)
  ensure
    d.close
  end

  def test_path
    d = Dir.open(@root)
    assert_equal(@root, d.path)
    assert_nil(Dir.allocate.path)
  ensure
    d.close
  end

  def test_set_pos
    d = Dir.open(@root)
    loop do
      i = d.pos
      break unless x = d.read
      d.pos = i
      assert_equal(x, d.read)
    end
  ensure
    d.close
  end

  def test_rewind
    d = Dir.open(@root)
    a = (0..5).map { d.read }
    d.rewind
    b = (0..5).map { d.read }
    assert_equal(a, b)
  ensure
    d.close
  end

  def test_class_chdir
    pwd = Dir.pwd
    setup_envs

    assert_raise(Errno::ENOENT) { Dir.chdir(@nodir) }
    assert_raise(ArgumentError) { Dir.chdir }
    ENV["HOME"] = pwd
    Dir.chdir do
      conflicting = /conflicting chdir during another chdir block\n^#{Regexp.quote(__FILE__)}:#{__LINE__-1}:/
      assert_warning(conflicting) { Dir.chdir(pwd) }

      assert_warning(conflicting) { Dir.chdir(@root) }
      assert_equal(@root, Dir.pwd)

      assert_warning(conflicting) { Dir.chdir(pwd) }

      assert_raise(RuntimeError) { Thread.new { Thread.current.report_on_exception = false; Dir.chdir(@root) }.join }
      assert_raise(RuntimeError) { Thread.new { Thread.current.report_on_exception = false; Dir.chdir(@root) { } }.join }

      assert_warning(conflicting) { Dir.chdir(pwd) }

      assert_warning(conflicting) { Dir.chdir(@root) }
      assert_equal(@root, Dir.pwd)

      assert_warning(conflicting) { Dir.chdir(pwd) }
      Dir.chdir(@root) do
        assert_equal(@root, Dir.pwd)
      end
      assert_equal(pwd, Dir.pwd)
    end

  ensure
    begin
      Dir.chdir(pwd)
    rescue
      abort("cannot return the original directory: #{ pwd }")
    end
  end

  def test_instance_chdir
    pwd = Dir.pwd
    dir = Dir.new(pwd)
    root_dir = Dir.new(@root)
    setup_envs

    ENV["HOME"] = pwd
    ret = root_dir.chdir do |*a|
      conflicting = /conflicting chdir during another chdir block\n^#{Regexp.quote(__FILE__)}:#{__LINE__-1}:/

      assert_empty(a)

      assert_warning(conflicting) { dir.chdir }
      assert_warning(conflicting) { root_dir.chdir }

      assert_equal(@root, Dir.pwd)

      assert_raise(RuntimeError) { Thread.new { Thread.current.report_on_exception = false; dir.chdir }.join }
      assert_raise(RuntimeError) { Thread.new { Thread.current.report_on_exception = false; dir.chdir{} }.join }

      assert_warning(conflicting) { dir.chdir }
      assert_equal(pwd, Dir.pwd)

      assert_warning(conflicting) { root_dir.chdir }
      assert_equal(@root, Dir.pwd)

      assert_warning(conflicting) { dir.chdir }

      root_dir.chdir do
        assert_equal(@root, Dir.pwd)
      end
      assert_equal(pwd, Dir.pwd)

      42
    end

    assert_separately(["-", @root], "#{<<~"begin;"}\n#{<<~'end;'}")
    begin;
      root = ARGV.shift

      $dir_warnings = []

      def Warning.warn(message)
        $dir_warnings << message
      end

      line2 = line1 = __LINE__; Dir.chdir(root) do
        line2 = __LINE__; Dir.chdir
      end

      message = $dir_warnings.shift
      assert_include(message, "#{__FILE__}:#{line2}:")
      assert_include(message, "#{__FILE__}:#{line1}:")
      assert_empty($dir_warnings)
    end;

    assert_equal(42, ret)
  ensure
    begin
      assert_equal(0, dir.chdir)
    rescue
      abort("cannot return the original directory: #{ pwd }")
    end
    dir.close
    root_dir.close
  end

  def test_chdir_conflict
    pwd = Dir.pwd
    q = Thread::Queue.new
    t = Thread.new do
      q.pop
      Dir.chdir(pwd) rescue $!
    end
    Dir.chdir(pwd) do
      q.push nil
      assert_instance_of(RuntimeError, t.value)
    end

    t = Thread.new do
      q.pop
      Dir.chdir(pwd){} rescue $!
    end
    Dir.chdir(pwd) do
      q.push nil
      assert_instance_of(RuntimeError, t.value)
    end
  end

  def test_chroot_nodir
    omit if RUBY_PLATFORM =~ /android/
    assert_raise(NotImplementedError, Errno::ENOENT, Errno::EPERM
		) { Dir.chroot(File.join(@nodir, "")) }
  end

  def test_close
    d = Dir.open(@root)
    d.close
    assert_nothing_raised(IOError) { d.close }
    assert_raise(IOError) { d.read }
  end

  def test_glob
    assert_equal((%w(.) + ("a".."z").to_a).map{|f| File.join(@root, f) },
                 Dir.glob(File.join(@root, "*"), File::FNM_DOTMATCH))
    assert_equal([@root] + ("a".."z").map {|f| File.join(@root, f) },
                 Dir.glob([@root, File.join(@root, "*")]))
    assert_equal([@root] + ("a".."z").map {|f| File.join(@root, f) },
                 Dir.glob([@root, File.join(@root, "*")], sort: false).sort)
    assert_equal([@root] + ("a".."z").map {|f| File.join(@root, f) },
                 Dir.glob([@root, File.join(@root, "*")], sort: true))
    assert_raise_with_message(ArgumentError, /nul-separated/) do
      Dir.glob(@root + "\0\0\0" + File.join(@root, "*"))
    end
    assert_raise_with_message(ArgumentError, /expected true or false/) do
      Dir.glob(@root, sort: 1)
    end
    assert_raise_with_message(ArgumentError, /expected true or false/) do
      Dir.glob(@root, sort: nil)
    end

    assert_equal(("a".."z").each_slice(2).map {|f,_| File.join(File.join(@root, f), "") },
                 Dir.glob(File.join(@root, "*/")))
    assert_equal([File.join(@root, '//a')], Dir.glob(@root + '//a'))

    FileUtils.touch(File.join(@root, "{}"))
    assert_equal(%w({} a).map{|f| File.join(@root, f) },
                 Dir.glob(File.join(@root, '{\{\},a}')))
    assert_equal([], Dir.glob(File.join(@root, '[')))
    assert_equal([], Dir.glob(File.join(@root, '[a-\\')))

    assert_equal([File.join(@root, "a")], Dir.glob(File.join(@root, 'a\\')))
    assert_equal(("a".."f").map {|f| File.join(@root, f) }, Dir.glob(File.join(@root, '[abc/def]')))

    open(File.join(@root, "}}{}"), "wb") {}
    open(File.join(@root, "}}a"), "wb") {}
    assert_equal(%w(}}{} }}a).map {|f| File.join(@root, f)}, Dir.glob(File.join(@root, '}}{\{\},a}')))
    assert_equal(%w(}}{} }}a b c).map {|f| File.join(@root, f)}, Dir.glob(File.join(@root, '{\}\}{\{\},a},b,c}')))
    assert_raise(ArgumentError) {
      Dir.glob([[@root, File.join(@root, "*")].join("\0")])
    }
  end

  def test_glob_recursive
    bug6977 = '[ruby-core:47418]'
    bug8006 = '[ruby-core:53108] [Bug #8006]'
    Dir.chdir(@root) do
      assert_include(Dir.glob("a/**/*", File::FNM_DOTMATCH), "a/.", bug8006)

      Dir.mkdir("a/b")
      assert_not_include(Dir.glob("a/**/*", File::FNM_DOTMATCH), "a/b/.")

      FileUtils.mkdir_p("a/b/c/d/e/f")
      assert_equal(["a/b/c/d/e/f"], Dir.glob("a/**/e/f"), bug6977)
      assert_equal(["a/b/c/d/e/f"], Dir.glob("a/**/d/e/f"), bug6977)
      assert_equal(["a/b/c/d/e/f"], Dir.glob("a/**/c/d/e/f"), bug6977)
      assert_equal(["a/b/c/d/e/f"], Dir.glob("a/**/b/c/d/e/f"), bug6977)
      assert_equal(["a/b/c/d/e/f"], Dir.glob("a/**/c/?/e/f"), bug6977)
      assert_equal(["a/b/c/d/e/f"], Dir.glob("a/**/c/**/d/e/f"), bug6977)
      assert_equal(["a/b/c/d/e/f"], Dir.glob("a/**/c/**/d/e/f"), bug6977)

      bug8283 = '[ruby-core:54387] [Bug #8283]'
      dirs = ["a/.x", "a/b/.y"]
      FileUtils.mkdir_p(dirs)
      dirs.map {|dir| open("#{dir}/z", "w") {}}
      assert_equal([], Dir.glob("a/**/z"), bug8283)
      assert_equal(["a/.x/z"], Dir.glob("a/**/.x/z"), bug8283)
      assert_equal(["a/.x/z"], Dir.glob("a/.x/**/z"), bug8283)
      assert_equal(["a/b/.y/z"], Dir.glob("a/**/.y/z"), bug8283)
    end
  end

  def test_glob_recursive_directory
    Dir.chdir(@root) do
      ['d', 'e'].each do |path|
        FileUtils.mkdir_p("c/#{path}/a/b/c")
        FileUtils.touch("c/#{path}/a/a.file")
        FileUtils.touch("c/#{path}/a/b/b.file")
        FileUtils.touch("c/#{path}/a/b/c/c.file")
      end
      bug15540 = '[ruby-core:91110] [Bug #15540]'
      assert_equal(["c/d/a/", "c/d/a/b/", "c/d/a/b/c/", "c/e/a/", "c/e/a/b/", "c/e/a/b/c/"],
                   Dir.glob('c/{d,e}/a/**/'), bug15540)

      assert_equal(["c/e/a/", "c/e/a/b/", "c/e/a/b/c/", "c/d/a/", "c/d/a/b/", "c/d/a/b/c/"],
                   Dir.glob('c/{e,d}/a/**/'))
    end
  end

  def test_glob_starts_with_brace
    Dir.chdir(@root) do
      bug15649 = '[ruby-core:91728] [Bug #15649]'
      assert_equal(["#{@root}/a", "#{@root}/b"],
                   Dir.glob("{#{@root}/a,#{@root}/b}"), bug15649)
    end
  end

  def test_glob_recursive_with_brace
    Dir.chdir(@root) do
      bug19042 = '[ruby-core:110220] [Bug #19042]'
      %w"c/dir_a c/dir_b c/dir_b/dir".each do |d|
        Dir.mkdir(d)
      end
      expected = %w"c/dir_a/file c/dir_b/dir/file"
      expected.each do |f|
        File.write(f, "")
      end
      assert_equal(expected, Dir.glob("**/{dir_a,dir_b/dir}/file"), bug19042)
    end
  end

  def test_glob_order
    Dir.chdir(@root) do
      assert_equal(["#{@root}/a", "#{@root}/b"], Dir.glob("#{@root}/[ba]"))
      assert_equal(["#{@root}/b", "#{@root}/a"], Dir.glob(%W"#{@root}/b #{@root}/a"))
      assert_equal(["#{@root}/b", "#{@root}/a"], Dir.glob("#{@root}/{b,a}"))
    end
    assert_equal(["a", "b"], Dir.glob("[ba]", base: @root))
    assert_equal(["b", "a"], Dir.glob(%W"b a", base: @root))
    assert_equal(["b", "a"], Dir.glob("{b,a}", base: @root))
  end

  if Process.const_defined?(:RLIMIT_NOFILE)
    def test_glob_too_may_open_files
      assert_separately([], "#{<<-"begin;"}\n#{<<-'end;'}", chdir: @root)
      begin;
        n = 16
        Process.setrlimit(Process::RLIMIT_NOFILE, n)
        files = []
        begin
          n.times {files << File.open('b')}
        rescue Errno::EMFILE, Errno::ENFILE => e
        end
        assert_raise(e.class) {
          Dir.glob('*')
        }
      end;
    end
  end

  def test_glob_base
    files = %w[a/foo.c c/bar.c]
    files.each {|n| File.write(File.join(@root, n), "")}
    Dir.mkdir(File.join(@root, "a/dir"))
    dirs = @dirs + %w[a/dir/]
    dirs.sort!

    assert_equal(files, Dir.glob("*/*.c", base: @root))
    assert_equal(files, Dir.chdir(@root) {Dir.glob("*/*.c", base: ".")})
    assert_equal(%w[foo.c], Dir.chdir(@root) {Dir.glob("*.c", base: "a")})
    assert_equal(files, Dir.chdir(@root) {Dir.glob("*/*.c", base: "")})
    assert_equal(files, Dir.chdir(@root) {Dir.glob("*/*.c", base: nil)})
    assert_equal(@dirs, Dir.glob("*/", base: @root))
    assert_equal(@dirs, Dir.chdir(@root) {Dir.glob("*/", base: ".")})
    assert_equal(%w[dir/], Dir.chdir(@root) {Dir.glob("*/", base: "a")})
    assert_equal(@dirs, Dir.chdir(@root) {Dir.glob("*/", base: "")})
    assert_equal(@dirs, Dir.chdir(@root) {Dir.glob("*/", base: nil)})
    assert_equal(dirs, Dir.glob("**/*/", base: @root))
    assert_equal(dirs, Dir.chdir(@root) {Dir.glob("**/*/", base: ".")})
    assert_equal(%w[dir/], Dir.chdir(@root) {Dir.glob("**/*/", base: "a")})
    assert_equal(dirs, Dir.chdir(@root) {Dir.glob("**/*/", base: "")})
    assert_equal(dirs, Dir.chdir(@root) {Dir.glob("**/*/", base: nil)})

    assert_equal(files, Dir.glob("*/*.c", base: @root, sort: false).sort)
    assert_equal(files, Dir.chdir(@root) {Dir.glob("*/*.c", base: ".", sort: false).sort})
    assert_equal(%w[foo.c], Dir.chdir(@root) {Dir.glob("*.c", base: "a", sort: false).sort})
    assert_equal(files, Dir.chdir(@root) {Dir.glob("*/*.c", base: "", sort: false).sort})
    assert_equal(files, Dir.chdir(@root) {Dir.glob("*/*.c", base: nil, sort: false).sort})
    assert_equal(@dirs, Dir.glob("*/", base: @root))
    assert_equal(@dirs, Dir.chdir(@root) {Dir.glob("*/", base: ".", sort: false).sort})
    assert_equal(%w[dir/], Dir.chdir(@root) {Dir.glob("*/", base: "a", sort: false).sort})
    assert_equal(@dirs, Dir.chdir(@root) {Dir.glob("*/", base: "", sort: false).sort})
    assert_equal(@dirs, Dir.chdir(@root) {Dir.glob("*/", base: nil, sort: false).sort})
    assert_equal(dirs, Dir.glob("**/*/", base: @root))
    assert_equal(dirs, Dir.chdir(@root) {Dir.glob("**/*/", base: ".", sort: false).sort})
    assert_equal(%w[dir/], Dir.chdir(@root) {Dir.glob("**/*/", base: "a", sort: false).sort})
    assert_equal(dirs, Dir.chdir(@root) {Dir.glob("**/*/", base: "", sort: false).sort})
    assert_equal(dirs, Dir.chdir(@root) {Dir.glob("**/*/", base: nil, sort: false).sort})
  end

  def test_glob_base_dir
    files = %w[a/foo.c c/bar.c]
    files.each {|n| File.write(File.join(@root, n), "")}
    Dir.mkdir(File.join(@root, "a/dir"))
    dirs = @dirs + %w[a/dir/]
    dirs.sort!

    assert_equal(files, Dir.open(@root) {|d| Dir.glob("*/*.c", base: d)})
    assert_equal(%w[foo.c], Dir.chdir(@root) {Dir.open("a") {|d| Dir.glob("*.c", base: d)}})
    assert_equal(@dirs, Dir.open(@root) {|d| Dir.glob("*/", base: d)})
    assert_equal(%w[dir/], Dir.chdir(@root) {Dir.open("a") {|d| Dir.glob("*/", base: d)}})
    assert_equal(dirs, Dir.open(@root) {|d| Dir.glob("**/*/", base: d)})
    assert_equal(%w[dir/], Dir.chdir(@root) {Dir.open("a") {|d| Dir.glob("**/*/", base: d)}})

    assert_equal(files, Dir.open(@root) {|d| Dir.glob("*/*.c", base: d, sort: false).sort})
    assert_equal(%w[foo.c], Dir.chdir(@root) {Dir.open("a") {|d| Dir.glob("*.c", base: d, sort: false).sort}})
    assert_equal(@dirs, Dir.open(@root) {|d| Dir.glob("*/", base: d, sort: false).sort})
    assert_equal(%w[dir/], Dir.chdir(@root) {Dir.open("a") {|d| Dir.glob("*/", base: d, sort: false).sort}})
    assert_equal(dirs, Dir.open(@root) {|d| Dir.glob("**/*/", base: d, sort: false).sort})
    assert_equal(%w[dir/], Dir.chdir(@root) {Dir.open("a") {|d| Dir.glob("**/*/", base: d, sort: false).sort}})
  end

  def test_glob_ignore_casefold_invalid_encoding
    bug14456 = "[ruby-core:85448]"
    filename = "\u00AAa123".encode('ISO-8859-1')
    File.write(File.join(@root, filename), "")
    matches = Dir.chdir(@root) {|d| Dir.glob("*a123".encode('UTF-8'), File::FNM_CASEFOLD)}
    assert_equal(1, matches.size, bug14456)
    matches.each{|f| f.force_encoding('ISO-8859-1')}
    # Handle MacOS/Windows, which saves under a different filename
    assert_include([filename, "\u00C2\u00AAa123".encode('ISO-8859-1')], matches.first, bug14456)
  end

  def assert_entries(entries, children_only = false)
    entries.sort!
    expected = ("a".."z").to_a
    expected = %w(. ..) + expected unless children_only
    assert_equal(expected, entries)
  end

  def test_entries
    assert_entries(Dir.open(@root) {|dir| dir.entries})
    assert_entries(Dir.entries(@root))
    assert_raise(ArgumentError) {Dir.entries(@root+"\0")}
    [Encoding::UTF_8, Encoding::ASCII_8BIT].each do |enc|
      assert_equal(enc, Dir.entries(@root, encoding: enc).first.encoding)
    end
  end

  def test_foreach
    assert_entries(Dir.open(@root) {|dir| dir.each.to_a})
    assert_entries(Dir.foreach(@root).to_a)
    assert_raise(ArgumentError) {Dir.foreach(@root+"\0").to_a}
    newdir = @root+"/new"
    e = Dir.foreach(newdir)
    assert_raise(Errno::ENOENT) {e.to_a}
    Dir.mkdir(newdir)
    File.write(newdir+"/a", "")
    assert_equal(%w[. .. a], e.to_a.sort)
    [Encoding::UTF_8, Encoding::ASCII_8BIT].each do |enc|
      e = Dir.foreach(newdir, encoding: enc)
      assert_equal(enc, e.to_a.first.encoding)
    end
  end

  def test_children
    assert_entries(Dir.open(@root) {|dir| dir.children}, true)
    assert_entries(Dir.children(@root), true)
    assert_raise(ArgumentError) {Dir.children(@root+"\0")}
    [Encoding::UTF_8, Encoding::ASCII_8BIT].each do |enc|
      assert_equal(enc, Dir.children(@root, encoding: enc).first.encoding)
    end
  end

  def test_each_child
    assert_entries(Dir.open(@root) {|dir| dir.each_child.to_a}, true)
    assert_entries(Dir.each_child(@root).to_a, true)
    assert_raise(ArgumentError) {Dir.each_child(@root+"\0").to_a}
    newdir = @root+"/new"
    e = Dir.each_child(newdir)
    assert_raise(Errno::ENOENT) {e.to_a}
    Dir.mkdir(newdir)
    File.write(newdir+"/a", "")
    assert_equal(%w[a], e.to_a)
    [Encoding::UTF_8, Encoding::ASCII_8BIT].each do |enc|
      e = Dir.each_child(newdir, encoding: enc)
      assert_equal(enc, e.to_a.first.encoding)
    end
  end

  def test_dir_enc
    dir = Dir.open(@root, encoding: "UTF-8")
    begin
      while name = dir.read
	assert_equal(Encoding.find("UTF-8"), name.encoding)
      end
    ensure
      dir.close
    end

    dir = Dir.open(@root, encoding: "ASCII-8BIT")
    begin
      while name = dir.read
	assert_equal(Encoding.find("ASCII-8BIT"), name.encoding)
      end
    ensure
      dir.close
    end
  end

  def test_unknown_keywords
    bug8060 = '[ruby-dev:47152] [Bug #8060]'
    assert_raise_with_message(ArgumentError, /unknown keyword/, bug8060) do
      Dir.open(@root, xawqij: "a") {}
    end
  end

  def test_symlink
    begin
      ["dummy", *"a".."z"].each do |f|
	File.symlink(File.join(@root, f),
		     File.join(@root, "symlink-#{ f }"))
      end
    rescue NotImplementedError, Errno::EACCES
      return
    end

    assert_equal([*"a".."z", *"symlink-a".."symlink-z"].each_slice(2).map {|f, _| File.join(@root, f + "/") }.sort,
		 Dir.glob(File.join(@root, "*/")))

    assert_equal([@root + "/", *[*"a".."z"].each_slice(2).map {|f, _| File.join(@root, f + "/") }],
                 Dir.glob(File.join(@root, "**/")))
  end

  def test_glob_metachar
    bug8597 = '[ruby-core:55764] [Bug #8597]'
    assert_empty(Dir.glob(File.join(@root, "<")), bug8597)
  end

  def test_glob_cases
    feature5994 = "[ruby-core:42469] [Feature #5994]"
    feature5994 << "\nDir.glob should return the filename with actual cases on the filesystem"
    Dir.chdir(File.join(@root, "a")) do
      open("FileWithCases", "w") {}
      return unless File.exist?("filewithcases")
      assert_equal(%w"FileWithCases", Dir.glob("filewithcases"), feature5994)
    end
    Dir.chdir(@root) do
      assert_equal(%w"a/FileWithCases", Dir.glob("A/filewithcases"), feature5994)
    end
  end

  def test_glob_super_root
    bug9648 = '[ruby-core:61552] [Bug #9648]'
    roots = Dir.glob("/*")
    assert_equal(roots.map {|n| "/..#{n}"}, Dir.glob("/../*"), bug9648)
  end

  if /mswin|mingw/ =~ RUBY_PLATFORM
    def test_glob_legacy_short_name
      bug10819 = '[ruby-core:67954] [Bug #10819]'
      bug11206 = '[ruby-core:69435] [Bug #11206]'
      omit unless /\A\w:/ =~ ENV["ProgramFiles"]
      short = "#$&/PROGRA~1"
      omit unless File.directory?(short)
      entries = Dir.glob("#{short}/Common*")
      assert_not_empty(entries, bug10819)
      long = File.expand_path(short)
      assert_equal(Dir.glob("#{long}/Common*"), entries, bug10819)
      wild = short.sub(/1\z/, '*')
      assert_not_include(Dir.glob(wild), long, bug11206)
      assert_include(Dir.glob(wild, File::FNM_SHORTNAME), long, bug10819)
      assert_empty(entries - Dir.glob("#{wild}/Common*", File::FNM_SHORTNAME), bug10819)
    end

    def test_home_windows
      setup_envs(%w[HOME USERPROFILE HOMEDRIVE HOMEPATH])

      ENV['HOME'] = "C:\\ruby\\home"
      assert_equal("C:/ruby/home", Dir.home)

      ENV['USERPROFILE'] = "C:\\ruby\\userprofile"
      assert_equal("C:/ruby/home", Dir.home)
      ENV.delete('HOME')
      assert_equal("C:/ruby/userprofile", Dir.home)

      ENV['HOMEDRIVE'] = "C:"
      ENV['HOMEPATH'] = "\\ruby\\homepath"
      assert_equal("C:/ruby/userprofile", Dir.home)
      ENV.delete('USERPROFILE')
      assert_equal("C:/ruby/homepath", Dir.home)
    end

    def test_home_at_startup_windows
      env = {'HOME' => "C:\\ruby\\home"}
      args = [env]
      assert_separately(args, "#{<<~"begin;"}\n#{<<~'end;'}")
      begin;
        assert_equal("C:/ruby/home", Dir.home)
      end;

      env['USERPROFILE'] = "C:\\ruby\\userprofile"
      assert_separately(args, "#{<<~"begin;"}\n#{<<~'end;'}")
      begin;
        assert_equal("C:/ruby/home", Dir.home)
      end;

      env['HOME'] = nil
      assert_separately(args, "#{<<~"begin;"}\n#{<<~'end;'}")
      begin;
        assert_equal("C:/ruby/userprofile", Dir.home)
      end;

      env['HOMEDRIVE'] = "C:"
      env['HOMEPATH'] = "\\ruby\\homepath"
      assert_separately(args, "#{<<~"begin;"}\n#{<<~'end;'}")
      begin;
        assert_equal("C:/ruby/userprofile", Dir.home)
      end;

      env['USERPROFILE'] = nil
      assert_separately(args, "#{<<~"begin;"}\n#{<<~'end;'}")
      begin;
        assert_equal("C:/ruby/homepath", Dir.home)
      end;
    end

    def test_children_long_name
      Dir.mktmpdir do |dirname|
        longest_possible_component = "b" * 255
        long_path = File.join(dirname, longest_possible_component)
        Dir.mkdir(long_path)
        File.write("#{long_path}/c", "")
        assert_equal(%w[c], Dir.children(long_path))
      ensure
        File.unlink("#{long_path}/c")
        Dir.rmdir(long_path)
      end
    rescue Errno::ENOENT
      omit "File system does not support long file name"
    end
  end

  def test_home
    setup_envs

    ENV["HOME"] = @nodir
    assert_nothing_raised(ArgumentError) do
      assert_equal(@nodir, Dir.home)
    end
    assert_nothing_raised(ArgumentError) do
      assert_equal(@nodir, Dir.home(""))
    end
    if user = ENV["USER"]
      tilde = windows? ? "~" : "~#{user}"
      assert_nothing_raised(ArgumentError) do
        assert_equal(File.expand_path(tilde), Dir.home(user))
      end
    end
    %W[no:such:user \u{7559 5b88}:\u{756a}].each do |user|
      assert_raise_with_message(ArgumentError, /#{user}/) {Dir.home(user)}
    end
  end

  if Encoding.find("filesystem") == Encoding::UTF_8
    # On Windows and macOS, file system encoding is always UTF-8.
    def test_home_utf8
      setup_envs

      ENV["HOME"] = "/\u{e4}~\u{1f3e0}"
      assert_equal("/\u{e4}~\u{1f3e0}", Dir.home)
    end
  end

  def test_symlinks_not_resolved
    Dir.mktmpdir do |dirname|
      Dir.chdir(dirname) do
        begin
          File.symlink('some-dir', 'dir-symlink')
        rescue NotImplementedError, Errno::EACCES
          return
        end

        Dir.mkdir('some-dir')
        File.write('some-dir/foo', 'some content')

        assert_equal [ 'dir-symlink', 'some-dir' ], Dir['*']
        assert_equal [ 'dir-symlink', 'some-dir', 'some-dir/foo' ], Dir['**/*']
      end
    end
  end

  def test_fileno
    Dir.open(".") {|d|
      if d.respond_to? :fileno
        assert_kind_of(Integer, d.fileno)
      else
        assert_raise(NotImplementedError) { d.fileno }
      end
    }
  end

  def test_for_fd
    if Dir.respond_to? :for_fd
      begin
        new_dir = Dir.new('..')
        for_fd_dir = Dir.for_fd(new_dir.fileno)
        assert_equal(new_dir.chdir{Dir.pwd}, for_fd_dir.chdir{Dir.pwd})
      ensure
        new_dir&.close
        if for_fd_dir
          assert_raise(Errno::EBADF) { for_fd_dir.close }
        end
      end
    else
      assert_raise(NotImplementedError) { Dir.for_fd(0) }
    end
  end

  def test_empty?
    assert_not_send([Dir, :empty?, @root])
    a = File.join(@root, "a")
    assert_send([Dir, :empty?, a])
    %w[A .dot].each do |tmp|
      tmp = File.join(a, tmp)
      open(tmp, "w") {}
      assert_not_send([Dir, :empty?, a])
      File.delete(tmp)
      assert_send([Dir, :empty?, a])
      Dir.mkdir(tmp)
      assert_not_send([Dir, :empty?, a])
      Dir.rmdir(tmp)
      assert_send([Dir, :empty?, a])
    end
    assert_raise(Errno::ENOENT) {Dir.empty?(@nodir)}
    assert_not_send([Dir, :empty?, File.join(@root, "b")])
    assert_raise(ArgumentError) {Dir.empty?(@root+"\0")}
  end

  def test_glob_gc_for_fd
    assert_separately(["-C", @root], "#{<<-"begin;"}\n#{<<-"end;"}", timeout: 3)
    begin;
      Process.setrlimit(Process::RLIMIT_NOFILE, 50)
      begin
        fs = []
        tap {tap {tap {(0..100).each {fs << open(IO::NULL)}}}}
      rescue Errno::EMFILE
      ensure
        fs.clear
      end
      list = Dir.glob("*")
      assert_not_empty(list)
      assert_equal([*"a".."z"], list)
    end;
  end if defined?(Process::RLIMIT_NOFILE)

  def test_glob_array_with_destructive_element
    args = Array.new(100, "")
    pat = Struct.new(:ary).new(args)
    args.push(pat, *Array.new(100) {"."*40})
    def pat.to_path
      ary.clear
      GC.start
      ""
    end
    assert_empty(Dir.glob(args))
  end
end
