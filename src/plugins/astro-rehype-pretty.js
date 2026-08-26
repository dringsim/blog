// modified from https://github.com/expressive-code/expressive-code/tree/main/packages/astro-expressive-code/src
import rehypePrettyCode from "rehype-pretty-code";
import { expressiveCodeConfig } from '../config/';

export function rehypePretty() {
	const integration = {
		name: 'astro-rehype-pretty',
		hooks: {
			'astro:config:setup': async (args) => {
				const { config: astroConfig, updateConfig } = args

				const markdownProcessor = (astroConfig.markdown)?.processor
                markdownProcessor.options.rehypePlugins.push(() => rehypePrettyCode(
                    {
                        theme: {
                            light: expressiveCodeConfig.lightTheme,
                            dark: expressiveCodeConfig.darkTheme,
                        },
                    }
                ))
                updateConfig({ markdown: { syntaxHighlight: false } })
			},
		},
	}

	return integration
}

export default rehypePretty
